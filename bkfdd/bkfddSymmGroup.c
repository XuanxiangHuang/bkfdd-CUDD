/**
  @file

  @ingroup bkfdd

  @brief Functions for BKFDD group sifting.

	@author Xuanxiang Huang

  @copyright
  Copyright (c) 2019-, Jinan University, Guangzhou, China.

  All rights reserved.

======================================================================
	All functions are originate from cuddGroup.c

	@Modification and Extension details
		1. Add functions for getting oet information and comparing oet information.
		2. Add functions for checking biconditional group information.
		3. Add functions for checking BKFDD's symmetric property.
		4. Add function for BKFDD's Group Sifting.
======================================================================

**********************************************************************
	@copyright@parblock
  Copyright (c) 1995-2015, Regents of the University of Colorado

  All rights reserved.

  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions
  are met:

  Redistributions of source code must retain the above copyright
  notice, this list of conditions and the following disclaimer.

  Redistributions in binary form must reproduce the above copyright
  notice, this list of conditions and the following disclaimer in the
  documentation and/or other materials provided with the distribution.

  Neither the name of the University of Colorado nor the names of its
  contributors may be used to endorse or promote products derived from
  this software without specific prior written permission.

  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
  COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
  BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
  LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
  LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
  ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
  POSSIBILITY OF SUCH DAMAGE.
  @endparblock
**********************************************************************

*/

#include "util.h"
#include "mtrInt.h"
#include "cuddInt.h"
#include "bkfddInt.h"

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

// biconditional group
#define G_TOP 1 // top of biconditional group
#define G_MID 2 // middle of biconditional group
#define G_BOT 3 // bottom of biconditional group

/* bkfdd (positive, negative)symmetry type, there are 4 structure:
	1. for two adjacent S-S level:
				(f11 == f00) || (f10 == f01)
	2. for two adjacent S-D level:
				(f11 \xor f01 == f10) || (f11 \xor f01 == f00)
	3. for two adjacent D-S level:
				(f11 \xor f10 == f01) || (f11 \xor f10 == f00)
	4. for two adjacent D-D leve:
				(f10 == f01) || (f10 \xor f01 == f00)
 */
#define S_S_SYM	0
#define S_D_SYM	1
#define D_S_SYM	2
#define D_D_SYM	3

/*---------------------------------------------------------------------------*/
/* Stucture declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/** \cond */

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/
static int ddUniqueCompareGroup (void const *ptrX, void const *ptrY);
static void ddCreateGroup (DdManager *table, int x, int y);
static int ddGroupSiftingAux (DdManager *table, int x, int xLow, int xHigh, BKFDD_CHKFP checkFunction);
static int ddGroupSiftingUp (DdManager *table, int y, int xLow, BKFDD_CHKFP checkFunction, Move **moves);
static int ddGroupSiftingDown (DdManager *table, int x, int xHigh, BKFDD_CHKFP checkFunction, Move **moves);
static int ddGroupMove (DdManager *table, int x, int y, Move **moves);
static int ddGroupMoveBackward (DdManager *table, int x, int y);
static int ddGroupSiftingBackward (DdManager *table, Move *moves, int size);
static void ddDissolveGroup (DdManager *table, int x, int y);
static int ddNoCheck (DdManager *table, int x, int y);
static int ddSecDiffCheck (DdManager *table, int x, int y);
static void getOET(DdManager * table, Oet *oet);
static int oetCompare(DdManager * table);
//static int checkBiGroup (DdManager * table, Oet * oet);
static int bkfddSymmCheck (DdManager *table, int x, int y);

/** \endcond */

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**
  @brief Sifts from treenode->low to treenode->high.

  @details Variable group is formed by function chooseBetterBKFDD.
	In BKFDD, variables associated with biconditonal expansions must NOT
	be the bottom of any group. In other words, each variable group must
	end with variables assocated with classical expansions.
	chooseBetterBKFDD is invoked after bkfddGroupSifting, which means
	the group of ith bkfddGroupSifting is determined by chooseBetterBKFDD
	after i-1th bkfddGroupSifting.

  @return 1 in case of success; 0 otherwise.

  @sideeffect None

	@NOTE Biconditional groups cannot be inserted, or dissolve during reordering.

*/
int
bkfddGroupSifting(
  DdManager * table,
  int  lower,
  int  upper,
	BKFDD_CHKFP checkFunction)
{
  IndexKey	*var;
  int		i,j,x,xInit;
  int		nvars;
  int		classes;
  int		result;
  int		*sifted;
  int		merged;
  int		dissolve;
#ifdef DD_STATS
  unsigned	previousSize;
#endif
  int		xindex;

	assert(table->oet1 == NULL);
	assert(table->oet2 == NULL);

  nvars = table->size;

	/* Order variables to sift. */
	sifted = NULL;
	var = ALLOC(IndexKey,nvars);
	if (var == NULL) {
		table->errorCode = CUDD_MEMORY_OUT;
		goto bkfddGroupSiftingOutOfMem;
	}
	sifted = ALLOC(int,nvars);
	if (sifted == NULL) {
		table->errorCode = CUDD_MEMORY_OUT;
		goto bkfddGroupSiftingOutOfMem;
	}
	
	// init OET
	table->oet1 = ALLOC(Oet,nvars);
	if (table->oet1 == NULL) {
		table->errorCode = CUDD_MEMORY_OUT;
		goto bkfddGroupSiftingOutOfMem;
	}

	table->oet2 = ALLOC(Oet,nvars);
	if (table->oet2 == NULL) {
		table->errorCode = CUDD_MEMORY_OUT;
		goto bkfddGroupSiftingOutOfMem;
	}

	assert(isCla(table->expansion[table->size-1]));

	// get OET before sifting
	getOET(table,table->oet1);

	/* Find Biconditional groups, which
		begin with variable assocated with Bi-expn, and
		end with variable assocated with Cla-expn. */
	for (i = 0; i < nvars; i ++) {
		assert(table->subtables[i].next == (unsigned)i);
	}
	for (i = 0; i < nvars; i ++) {
		if (isBi(table->expansion[i])) {
			int gtop = i;
			while (isBi(table->expansion[i])) {
				table->subtables[i].next = i+1;
				i ++;
			}
			assert(isCla(table->expansion[i]));
			table->subtables[i].next = gtop;
		}
	}

	/* We consider only one representative(bottom variable) for each group. */
	for (i = 0, classes = 0; i < nvars; i++) {
		sifted[i] = 0;
		x = table->perm[i]; // get level of i-th index variable
		if ((unsigned) x >= table->subtables[x].next) { // find level of bottom variable
			assert(isCla(table->expansion[x])); // bottom variable must assocatied with Cla-expn.
			var[classes].index = i;
			/* using total node count of whole group instead of bottom level. */
			if ((unsigned) x == table->subtables[x].next) {
				// single variable group
				var[classes].keys = table->subtables[x].keys;
			} else {
				// Biconditional group
				unsigned int sum = table->subtables[x].keys;
				int lvl = (int)table->subtables[x].next; // get top level of group
				while (lvl < x) {
					sum += table->subtables[lvl].keys;
					lvl ++;					
				}
				var[classes].keys = sum;
			}
			classes++;
		}
	}

	util_qsort(var, classes, sizeof(IndexKey), ddUniqueCompareGroup);

	/* Now sift. */
	for (i = 0; i < classes; i++) {
		if (table->ddTotalNumberSwapping >= table->siftMaxSwap)
			break;
		if (util_cpu_time() - table->startTime + table->reordTime
		> table->timeLimit) {
			table->autoDyn = 0; /* prevent further reordering */
			break;
		}
		if (table->terminationCallback != NULL &&
		table->terminationCallback(table->tcbArg)) {
			table->autoDyn = 0; /* prevent further reordering */
			break;
		}
		xindex = var[i].index; // xindex is bottom variable
		if (sifted[xindex] == 1) /* variable already sifted as part of group */
			continue;
		x = table->perm[xindex]; /* find current level of this variable */

		if (x < lower || x > upper || table->subtables[x].bindVar == 1)
			continue;
#ifdef DD_STATS
		previousSize = table->keys - table->isolated;
#endif

		/* x is bottom of group, next level of bottom variable is top of group */
		assert((unsigned) x >= table->subtables[x].next);
		assert(isCla(table->expansion[x]));

		if ((unsigned) x == table->subtables[x].next) {
		/* Single variable group, use symcheck to merge more group into it,
			biconditional groups probably be merged during sifting, 
			be careful when dissolving it. */
			dissolve = 1;
			result = ddGroupSiftingAux(table,x,lower,upper,checkFunction); // symm better or extsymm better ?
		} else {
		/* Treat Biconditional group as whole and don't merge any group into it */
			dissolve = 0;
			result = ddGroupSiftingAux(table,x,lower,upper,ddNoCheck);
		}
		if (!result) goto bkfddGroupSiftingOutOfMem;

		/* check for aggregation, variable of x level has been reordered. */
		merged = 0;
		x = table->perm[xindex]; /* find current level */
		if ((unsigned) x == table->subtables[x].next) { /* not part of a group */
			assert(isCla(table->expansion[x])); // two Cla-expn group
			/* If var of x-level and x+1-level are both single var group,
			Then check whether or not to merge these two adjacent variables. */
			if (x != upper && sifted[table->invperm[x+1]] == 0 &&
			(unsigned) x+1 == table->subtables[x+1].next) {
				assert(isCla(table->expansion[x+1])); // two Cla-expn group
				if (ddSecDiffCheck(table,x,x+1)) {
					merged =1;
					ddCreateGroup(table,x,x+1); // now we get x or (x,x+1)
				}
			}
			/* If var of x-1-level is a single var group,
			Then check whether or not to add it to x's group. */
			if (x != lower && sifted[table->invperm[x-1]] == 0 &&
			(unsigned) x-1 == table->subtables[x-1].next) {
				assert(isCla(table->expansion[x-1])); // two Cla-expn group
				if (ddSecDiffCheck(table,x-1,x)) {
					merged =1;
					ddCreateGroup(table,x-1,x); // now we get (x-1,x) or (x-1,x,x+1)
				}
			}
			/* All possible x-group in { x, (x-1,x), (x,x+1), (x-1,x,x+1) }
				and they are all Classical group */
		}

		if (merged) { /* a new Classical group was created */
			/* move x to bottom of group */
			while ((unsigned) x < table->subtables[x].next)
				x = table->subtables[x].next;
			/* sift, reorder newly created x-group. Don't merge group into it. */
			result = ddGroupSiftingAux(table,x,lower,upper,ddNoCheck);

			if (!result) goto bkfddGroupSiftingOutOfMem;
#ifdef DD_STATS
			if (table->keys < previousSize + table->isolated) {
			(void) fprintf(table->out,"_");
			} else if (table->keys > previousSize + table->isolated) {
			(void) fprintf(table->out,"^");
			} else {
			(void) fprintf(table->out,"*");
			}
			fflush(table->out);
		} else {
			if (table->keys < previousSize + table->isolated) {
			(void) fprintf(table->out,"-");
			} else if (table->keys > previousSize + table->isolated) {
			(void) fprintf(table->out,"+");
			} else {
			(void) fprintf(table->out,"=");
			}
			fflush(table->out);
#endif
		}

		/* Mark variables in the group just sifted. */
		x = table->perm[xindex];
		if ((unsigned) x != table->subtables[x].next) {
			xInit = x;
			do {
				j = table->invperm[x];
				sifted[j] = 1;
				x = table->subtables[x].next;
			} while (x != xInit);
			assert(x == xInit);
			/* Dissolve the group if it was created. 
				BUT We don't dissolve ANY Biconditional group.
				Only Classical group will be dissolve. */
			if (dissolve) {
				do {
					j = table->subtables[x].next;
					if (isCla(table->expansion[x])) {
						// whether it is single group or bottom of biconditional group
						int idx = table->invperm[x];
						assert(isCla(table->oet1[idx].expn));
						if ( (table->oet1[idx].top_mid_bot == -1) &&
								(table->oet1[idx].nextIdx == -1) ) {
							assert(table->oet1[idx].sv == -1);
							table->subtables[x].next = x; // dissolve single grouop
						} else {
							assert(table->oet1[idx].top_mid_bot == G_BOT);
							assert(table->oet1[table->oet1[idx].nextIdx].top_mid_bot == G_TOP);
							// fix biconditional group
							table->subtables[x].next = table->perm[table->oet1[idx].nextIdx];
						}
					}
					x = j;
				} while (x != xInit);
			}
		}
		
#ifdef DD_DEBUG
		if (table->enableExtraDebug > 0)
			(void) fprintf(table->out,"bkfddGroupSifting:");
#endif

	} /* for */

	assert(isCla(table->expansion[table->size-1]));

	getOET(table,table->oet2);
	assert(oetCompare(table) == 1);

	// dissolve all group
	for (i = 0; i < nvars; i++)
		table->subtables[i].next = i;

	FREE(table->oet1);
	FREE(table->oet2);
	FREE(sifted);
	FREE(var);
	return(1);

bkfddGroupSiftingOutOfMem:
	if (var != NULL)	FREE(var);
	if (sifted != NULL)	FREE(sifted);
	if (table->oet1 != NULL)	FREE(table->oet1);
	if (table->oet2 != NULL)	FREE(table->oet2);

	// dissolve all group
	for (i = 0; i < nvars; i++)
		table->subtables[i].next = i;

	return(0);

} /* end of bkfddGroupSifting */


/**
  @brief Sifts from treenode->low to treenode->high.

  @details Variable group is formed by function chooseBetterBKFDD.
	In BKFDD, variables associated with biconditonal expansions must NOT
	be the bottom of any group. In other words, each variable group must
	end with variables assocated with classical expansions.
	chooseBetterBKFDD is invoked after bkfddSymmSifting, which means
	the group of ith bkfddSymmSifting is determined by chooseBetterBKFDD
	after i-1th bkfddSymmSifting.

  @return 1 in case of success; 0 otherwise.

  @sideeffect None

	@NOTE Biconditional groups cannot be inserted, or dissolve during reordering.

*/
int
bkfddSymmSifting(
  DdManager * table,
  int  lower,
  int  upper)
{
  IndexKey	*var;
  int		i,j,x,xInit;
  int		nvars;
  int		classes;
  int		result;
  int		*sifted;
  int		dissolve;
#ifdef DD_STATS
  unsigned	previousSize;
#endif
  int		xindex;

	assert(table->oet1 == NULL);
	assert(table->oet2 == NULL);

  nvars = table->size;

	/* Order variables to sift. */
	sifted = NULL;
	var = ALLOC(IndexKey,nvars);
	if (var == NULL) {
		table->errorCode = CUDD_MEMORY_OUT;
		goto bkfddSymmSiftingOutOfMem;
	}
	sifted = ALLOC(int,nvars);
	if (sifted == NULL) {
		table->errorCode = CUDD_MEMORY_OUT;
		goto bkfddSymmSiftingOutOfMem;
	}
	
	// init OET
	table->oet1 = ALLOC(Oet,nvars);
	if (table->oet1 == NULL) {
		table->errorCode = CUDD_MEMORY_OUT;
		goto bkfddSymmSiftingOutOfMem;
	}

	table->oet2 = ALLOC(Oet,nvars);
	if (table->oet2 == NULL) {
		table->errorCode = CUDD_MEMORY_OUT;
		goto bkfddSymmSiftingOutOfMem;
	}

	assert(isCla(table->expansion[table->size-1]));

	// get OET before sifting
	getOET(table,table->oet1);

	/* Find Biconditional groups, which
		begin with variable assocated with Bi-expn, and
		end with variable assocated with Cla-expn. */
	for (i = 0; i < nvars; i ++) {
		assert(table->subtables[i].next == (unsigned)i);
	}
	for (i = 0; i < nvars; i ++) {
		if (isBi(table->expansion[i])) {
			int gtop = i;
			while (isBi(table->expansion[i])) {
				table->subtables[i].next = i+1;
				i ++;
			}
			assert(isCla(table->expansion[i]));
			table->subtables[i].next = gtop;
		}
	}

	/* We consider only one representative(bottom variable) for each group. */
	for (i = 0, classes = 0; i < nvars; i++) {
		sifted[i] = 0;
		x = table->perm[i]; // get level of i-th index variable
		if ((unsigned) x >= table->subtables[x].next) { // find level of bottom variable
			assert(isCla(table->expansion[x])); // bottom variable must assocatied with Cla-expn.
			var[classes].index = i;
			/* using total node count of whole group instead of bottom level. */
			if ((unsigned) x == table->subtables[x].next) {
				// single variable group
				var[classes].keys = table->subtables[x].keys;
			} else {
				// Biconditional group
				unsigned int sum = table->subtables[x].keys;
				int lvl = (int)table->subtables[x].next; // get top level of group
				while (lvl < x) {
					sum += table->subtables[lvl].keys;
					lvl ++;					
				}
				var[classes].keys = sum;
			}
			classes++;
		}
	}

	util_qsort(var, classes, sizeof(IndexKey), ddUniqueCompareGroup);

	/* Now sift. */
	for (i = 0; i < classes; i++) {
		if (table->ddTotalNumberSwapping >= table->siftMaxSwap)
			break;
		if (util_cpu_time() - table->startTime + table->reordTime
		> table->timeLimit) {
			table->autoDyn = 0; /* prevent further reordering */
			break;
		}
		if (table->terminationCallback != NULL &&
		table->terminationCallback(table->tcbArg)) {
			table->autoDyn = 0; /* prevent further reordering */
			break;
		}
		xindex = var[i].index; // xindex is bottom variable
		if (sifted[xindex] == 1) /* variable already sifted as part of group */
			continue;
		x = table->perm[xindex]; /* find current level of this variable */

		if (x < lower || x > upper || table->subtables[x].bindVar == 1)
			continue;
#ifdef DD_STATS
		previousSize = table->keys - table->isolated;
#endif

		/* x is bottom of group, next level of bottom variable is top of group */
		assert((unsigned) x >= table->subtables[x].next);
		assert(isCla(table->expansion[x]));

		if ((unsigned) x == table->subtables[x].next) {
		/* Single variable group, use symcheck to merge more group into it,
			biconditional groups probably be merged during sifting, 
			be careful when dissolving it. */
			dissolve = 1;
			result = ddGroupSiftingAux(table,x,lower,upper,bkfddSymmCheck);
		} else {
		/* Treat Biconditional group as whole and don't merge any group into it */
			dissolve = 0;
			result = ddGroupSiftingAux(table,x,lower,upper,ddNoCheck);
		}
		if (!result) goto bkfddSymmSiftingOutOfMem;

		/* Mark variables in the group just sifted. */
		x = table->perm[xindex];
		if ((unsigned) x != table->subtables[x].next) {
			xInit = x;
			do {
				j = table->invperm[x];
				sifted[j] = 1;
				x = table->subtables[x].next;
			} while (x != xInit);
			assert(x == xInit);
			/* Dissolve the group if it was created. 
				BUT We don't dissolve ANY Biconditional group.
				Only Classical group will be dissolve. */
			if (dissolve) {
				do {
					j = table->subtables[x].next;
					if (isCla(table->expansion[x])) {
						// whether it is single group or bottom of biconditional group
						int idx = table->invperm[x];
						assert(isCla(table->oet1[idx].expn));
						if ( (table->oet1[idx].top_mid_bot == -1) &&
								(table->oet1[idx].nextIdx == -1) ) {
							assert(table->oet1[idx].sv == -1);
							table->subtables[x].next = x; // dissolve single grouop
						} else {
							assert(table->oet1[idx].top_mid_bot == G_BOT);
							assert(table->oet1[table->oet1[idx].nextIdx].top_mid_bot == G_TOP);
							// fix biconditional group
							table->subtables[x].next = table->perm[table->oet1[idx].nextIdx];
						}
					}
					x = j;
				} while (x != xInit);
			}
		}
		
#ifdef DD_DEBUG
		if (table->enableExtraDebug > 0)
			(void) fprintf(table->out,"bkfddSymmSifting:");
#endif

	} /* for */

	assert(isCla(table->expansion[table->size-1]));

	getOET(table,table->oet2);
	assert(oetCompare(table) == 1);

	// dissolve all group
	for (i = 0; i < nvars; i++)
		table->subtables[i].next = i;

	FREE(table->oet1);
	FREE(table->oet2);
	FREE(sifted);
	FREE(var);
	return(1);

bkfddSymmSiftingOutOfMem:
	if (var != NULL)	FREE(var);
	if (sifted != NULL)	FREE(sifted);
	if (table->oet1 != NULL)	FREE(table->oet1);
	if (table->oet2 != NULL)	FREE(table->oet2);

	// dissolve all group
	for (i = 0; i < nvars; i++)
		table->subtables[i].next = i;

	return(0);

} /* end of bkfddSymmSifting */


/** Simple group sifting, no mergeing. */
int
bkfddGroupSifting_noMerge(
  DdManager * table,
  int  lower,
  int  upper)
{
  IndexKey	*var;
  int		i,j,x,xInit;
  int		nvars;
  int		classes;
  int		result;
  int		*sifted;
#ifdef DD_STATS
  unsigned	previousSize;
#endif
  int		xindex;

	assert(table->oet1 == NULL);
	assert(table->oet2 == NULL);

  nvars = table->size;

	/* Order variables to sift. */
	sifted = NULL;
	var = ALLOC(IndexKey,nvars);
	if (var == NULL) {
		table->errorCode = CUDD_MEMORY_OUT;
		goto bkfddGroupSiftingOutOfMem;
	}
	sifted = ALLOC(int,nvars);
	if (sifted == NULL) {
		table->errorCode = CUDD_MEMORY_OUT;
		goto bkfddGroupSiftingOutOfMem;
	}
	
	// init OET
	table->oet1 = ALLOC(Oet,nvars);
	if (table->oet1 == NULL) {
		table->errorCode = CUDD_MEMORY_OUT;
		goto bkfddGroupSiftingOutOfMem;
	}

	table->oet2 = ALLOC(Oet,nvars);
	if (table->oet2 == NULL) {
		table->errorCode = CUDD_MEMORY_OUT;
		goto bkfddGroupSiftingOutOfMem;
	}

	assert(isCla(table->expansion[table->size-1]));

	// get OET before sifting
	getOET(table,table->oet1);

	/* Find Biconditional groups, which
		begin with variable assocated with Bi-expn, and
		end with variable assocated with Cla-expn. */
	for (i = 0; i < nvars; i ++) {
		assert(table->subtables[i].next == (unsigned)i);
	}
	for (i = 0; i < nvars; i ++) {
		if (isBi(table->expansion[i])) {
			int gtop = i;
			while (isBi(table->expansion[i])) {
				table->subtables[i].next = i+1;
				i ++;
			}
			assert(isCla(table->expansion[i]));
			table->subtables[i].next = gtop;
		}
	}

	/* We consider only one representative(bottom variable) for each group. */
	for (i = 0, classes = 0; i < nvars; i++) {
		sifted[i] = 0;
		x = table->perm[i]; // get level of i-th index variable
		if ((unsigned) x >= table->subtables[x].next) { // find level of bottom variable
			assert(isCla(table->expansion[x])); // bottom variable must assocatied with Cla-expn.
			var[classes].index = i;
			/* using total node count of whole group instead of bottom level. */
			if ((unsigned) x == table->subtables[x].next) {
				// single variable group
				var[classes].keys = table->subtables[x].keys;
			} else {
				// Biconditional group
				unsigned int sum = table->subtables[x].keys;
				int lvl = (int)table->subtables[x].next; // get top level of group
				while (lvl < x) {
					sum += table->subtables[lvl].keys;
					lvl ++;					
				}
				var[classes].keys = sum;
			}
			classes++;
		}
	}

	util_qsort(var, classes, sizeof(IndexKey), ddUniqueCompareGroup);

	/* Now sift. */
	for (i = 0; i < classes; i++) {
		if (table->ddTotalNumberSwapping >= table->siftMaxSwap)
			break;
		if (util_cpu_time() - table->startTime + table->reordTime
		> table->timeLimit) {
			table->autoDyn = 0; /* prevent further reordering */
			break;
		}
		if (table->terminationCallback != NULL &&
		table->terminationCallback(table->tcbArg)) {
			table->autoDyn = 0; /* prevent further reordering */
			break;
		}
		xindex = var[i].index; // xindex is bottom variable
		if (sifted[xindex] == 1) /* variable already sifted as part of group */
			continue;
		x = table->perm[xindex]; /* find current level of this variable */

		if (x < lower || x > upper || table->subtables[x].bindVar == 1)
			continue;
#ifdef DD_STATS
		previousSize = table->keys - table->isolated;
#endif

		/* x is bottom of group, next level of bottom variable is top of group */
		assert((unsigned) x >= table->subtables[x].next);
		assert(isCla(table->expansion[x]));

		result = ddGroupSiftingAux(table,x,lower,upper,ddNoCheck);

		if (!result) goto bkfddGroupSiftingOutOfMem;

		/* Mark variables in the group just sifted. */
		x = table->perm[xindex];
		if ((unsigned) x != table->subtables[x].next) {
			xInit = x;
			do {
				j = table->invperm[x];
				sifted[j] = 1;
				x = table->subtables[x].next;
			} while (x != xInit);
			assert(x == xInit);
		}
		
#ifdef DD_DEBUG
		if (table->enableExtraDebug > 0)
			(void) fprintf(table->out,"bkfddGroupSifting:");
#endif

	} /* for */

	assert(isCla(table->expansion[table->size-1]));

	getOET(table,table->oet2);
	assert(oetCompare(table) == 1);

	// dissolve all group
	for (i = 0; i < nvars; i++)
		table->subtables[i].next = i;

	FREE(table->oet1);
	FREE(table->oet2);
	FREE(sifted);
	FREE(var);
	return(1);

bkfddGroupSiftingOutOfMem:
	if (var != NULL)	FREE(var);
	if (sifted != NULL)	FREE(sifted);
	if (table->oet1 != NULL)	FREE(table->oet1);
	if (table->oet2 != NULL)	FREE(table->oet2);

	// dissolve all group
	for (i = 0; i < nvars; i++)
		table->subtables[i].next = i;

	return(0);

} /* end of bkfddGroupSifting_noMerge */


/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/


/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/


/**
  @brief Comparison function used by qsort.

  @details Comparison function used by qsort to order the variables
  according to the number of keys in the subtables.

  @return the difference in number of keys between the two variables
  being compared.

  @sideeffect None

*/
static int
ddUniqueCompareGroup(
  void const * ptrX,
  void const * ptrY)
{
	IndexKey const * pX = (IndexKey const *) ptrX;
	IndexKey const * pY = (IndexKey const *) ptrY;

  return(pY->keys - pX->keys);

} /* end of ddUniqueCompareGroup */


/**
  @brief Creates a group encompassing variables from x to y in the
  %DD table.

  @details In the current implementation it must be y == x+1.

  @sideeffect None

*/
static void
ddCreateGroup(
  DdManager * table,
  int  x,
  int  y)
{
  int  gybot;

  assert(y == x+1);

	assert((unsigned)x == table->subtables[x].next);

	/* Find bottom of second group. */
	gybot = y;
	while ((unsigned) gybot < table->subtables[gybot].next) // ends when gybot > next
		gybot = table->subtables[gybot].next;

	/* Link groups. */
	table->subtables[x].next = y;
	table->subtables[gybot].next = x; // x must be single variable group

	return;

} /* end of ddCreateGroup */


/**
  @brief Sifts one variable up and down until it has taken all
  positions. Checks for aggregation.

  @details There may be at most two sweeps, even if the group grows.
  Assumes that x is either an isolated variable, or it is the bottom
  of a group. All groups may not have been found. The variable being
  moved is returned to the best position seen during sifting.

  @return 1 in case of success; 0 otherwise.

  @sideeffect None

*/
static int
ddGroupSiftingAux(
  DdManager * table,
  int  x,
  int  xLow,
  int  xHigh,
  BKFDD_CHKFP checkFunction)
{
  Move *move;
  Move *moves;	/* list of moves */
  int  initialSize;
  int  result;
  int  y;
  int  topbot;

#ifdef DD_DEBUG
  if (table->enableExtraDebug > 0)
		(void) fprintf(table->out,
		"ddGroupSiftingAux from %d to %d\n",xLow,xHigh);
#endif
	assert((unsigned) x >= table->subtables[x].next); /* x is bottom of group */

  table->originalSize = (table->keys - table->isolated);
  initialSize = (int) table->originalSize;
  moves = NULL;

	/* If we have a singleton, we check for aggregation in both
	** directions before we sift. 
	** x itself is single variable group, it may merged into biconditional group.
	*/
	if ((unsigned) x == table->subtables[x].next) {
		/* Will go down first, unless x == xHigh:
		** Look for aggregation above x.
		*/
		for (y = x; y > xLow; y--) { // x is always the bottom of new created group
			if (!checkFunction(table,y-1,y))
				break;
			topbot = table->subtables[y-1].next; /* find top of y-1's group */
			table->subtables[y-1].next = y;
			/* x is bottom of group so its next is top of y-1's group */
			table->subtables[x].next = topbot;
			y = topbot + 1; /* add 1 for y--; new y is top of group */
		}
		/* Will go up first unless x == xlow:
		** Look for aggregation below x.
		*/
		for (y = x; y < xHigh; y++) {
			if (!checkFunction(table,y,y+1))
				break;
			/* find bottom of y+1's group */
			topbot = y + 1;
			while ((unsigned) topbot < table->subtables[topbot].next) {
				topbot = table->subtables[topbot].next;
			}
			table->subtables[topbot].next = table->subtables[y].next;
			table->subtables[y].next = y + 1;
			y = topbot - 1; /* subtract 1 for y++; new y is bottom of group */
		}
	}

	/* Now x may be in the middle of a group.
	** Find bottom of x's group.
	*/
	while ((unsigned) x < table->subtables[x].next)
		x = table->subtables[x].next;

	assert(isCla(table->expansion[x]));

	if (x == xLow) { /* Sift down */
#ifdef DD_DEBUG
		/* x must be a singleton */
		assert((unsigned) x == table->subtables[x].next);
#endif
		if (x == xHigh) return(1);	/* just one variable */

		if (!ddGroupSiftingDown(table,x,xHigh,checkFunction,&moves))
			goto ddGroupSiftingAuxOutOfMem;

		/* at this point x == xHigh, unless early term */

		/* move backward and stop at best position */
		result = ddGroupSiftingBackward(table,moves,initialSize);

#ifdef DD_DEBUG
		assert(table->keys - table->isolated <= (unsigned) initialSize);
#endif
		if (!result) goto ddGroupSiftingAuxOutOfMem;

	} else if (cuddNextHigh(table,x) > xHigh) { /* Sift up */
#ifdef DD_DEBUG
		/* x is bottom of group */
		assert((unsigned) x >= table->subtables[x].next);
#endif
		/* Find top of x's group */
		x = table->subtables[x].next;

		if (!ddGroupSiftingUp(table,x,xLow,checkFunction,&moves))
			goto ddGroupSiftingAuxOutOfMem;

		/* at this point x == xLow, unless early term */

		/* move backward and stop at best position */
		result = ddGroupSiftingBackward(table,moves,initialSize);

#ifdef DD_DEBUG
		assert(table->keys - table->isolated <= (unsigned) initialSize);
#endif
		if (!result) goto ddGroupSiftingAuxOutOfMem;

	} else if (x - xLow > xHigh - x) { /* must go down first: shorter */
		if (!ddGroupSiftingDown(table,x,xHigh,checkFunction,&moves))
			goto ddGroupSiftingAuxOutOfMem;

		/* at this point x == xHigh, unless early term */

		/* Find top of group */
		if (moves) {
			x = moves->y;
		}
		while ((unsigned) x < table->subtables[x].next)
			x = table->subtables[x].next;
		// reach bottom of group
		assert((unsigned)x >= table->subtables[x].next);
		// reach top of group
		x = table->subtables[x].next;
#ifdef DD_DEBUG
		/* x should be the top of a group */
		assert((unsigned) x <= table->subtables[x].next);
#endif
		if (!ddGroupSiftingUp(table,x,xLow,checkFunction,&moves))
			goto ddGroupSiftingAuxOutOfMem;

		/* move backward and stop at best position */
		result = ddGroupSiftingBackward(table,moves,initialSize);

#ifdef DD_DEBUG
		assert(table->keys - table->isolated <= (unsigned) initialSize);
#endif
		if (!result) goto ddGroupSiftingAuxOutOfMem;

	} else { /* moving up first: shorter */
		/* Find top of x's group */
		x = table->subtables[x].next;

		if (!ddGroupSiftingUp(table,x,xLow,checkFunction,&moves))
			goto ddGroupSiftingAuxOutOfMem;
		/* at this point x == xHigh, unless early term */

		if (moves) {
			x = moves->x;
		}
		while ((unsigned) x < table->subtables[x].next)
			x = table->subtables[x].next;
#ifdef DD_DEBUG
		/* x is bottom of a group */
		assert((unsigned) x >= table->subtables[x].next);
#endif
		if (!ddGroupSiftingDown(table,x,xHigh,checkFunction,&moves))
			goto ddGroupSiftingAuxOutOfMem;

		/* move backward and stop at best position */
		result = ddGroupSiftingBackward(table,moves,initialSize);

#ifdef DD_DEBUG
		assert(table->keys - table->isolated <= (unsigned) initialSize);
#endif
		if (!result) goto ddGroupSiftingAuxOutOfMem;
	}

	while (moves != NULL) {
		move = moves->next;
		cuddDeallocMove(table, moves);
		moves = move;
	}

	return(1);

ddGroupSiftingAuxOutOfMem:
	while (moves != NULL) {
		move = moves->next;
		cuddDeallocMove(table, moves);
		moves = move;
	}

	return(0);

} /* end of ddGroupSiftingAux */


/**
  @brief Sifts up a variable until either it reaches position xLow
  or the size of the %DD heap increases too much.

  @details Assumes that y is the top of a group (or a singleton).
  Checks y for aggregation to the adjacent variables. Records all the
  moves that are appended to the list of moves received as input and
  returned as a side effect.

  @return 1 in case of success; 0 otherwise.

  @sideeffect None

*/
static int
ddGroupSiftingUp(
  DdManager * table,
  int  y,
  int  xLow,
  BKFDD_CHKFP checkFunction,
  Move ** moves)
{
  Move *move;
  int  x;
  int  size;
  int  i;
  int  gxtop,gybot;
  int  limitSize;
  int  xindex, yindex;
  int  zindex;
  int  z;
  unsigned int isolated;
  int  L;	/* lower bound on DD size */

#ifdef DD_DEBUG
  int  checkL;
#endif

  yindex = table->invperm[y];

	/* Initialize the lower bound.
	** The part of the DD below the bottom of y's group will not change.
	** The part of the DD above y that does not interact with any
	** variable of y's group will not change.
	** The rest may vanish in the best case, except for
	** the nodes at level xLow, which will not vanish, regardless.
	** What we use here is not really a lower bound, because we ignore
	** the interactions with all variables except y.
	*/
	limitSize = L = (int) (table->keys - table->isolated);
	gybot = y;
	while ((unsigned) gybot < table->subtables[gybot].next)
		gybot = table->subtables[gybot].next;

	assert((unsigned)y == table->subtables[gybot].next); // y is top of group

	for (z = xLow + 1; z <= gybot; z++) {
		zindex = table->invperm[z];
		if (zindex == yindex || cuddTestInteract(table,zindex,yindex)) {
			isolated = Cudd_Regular(table->vars[zindex])->ref == 1;
			L -= table->subtables[z].keys - isolated;
		}
	}

	x = cuddNextLow(table,y);
	while (x >= xLow && L <= limitSize) {
#ifdef DD_DEBUG
		gybot = y;
		while ((unsigned) gybot < table->subtables[gybot].next)
			gybot = table->subtables[gybot].next;
		checkL = table->keys - table->isolated;
		for (z = xLow + 1; z <= gybot; z++) {
			zindex = table->invperm[z];
			if (zindex == yindex || cuddTestInteract(table,zindex,yindex)) {
				isolated = Cudd_Regular(table->vars[zindex])->ref == 1;
				checkL -= table->subtables[z].keys - isolated;
			}
		}
		if (table->enableExtraDebug > 0 && L != checkL) {
			(void) fprintf(table->out,
			"Inaccurate lower bound: L = %d checkL = %d\n",
			L, checkL);
		}
#endif

		gxtop = table->subtables[x].next;
		if (checkFunction(table,x,y)) {
			/* Group found, attach groups */
			table->subtables[x].next = y;
			i = table->subtables[y].next;
			while (table->subtables[i].next != (unsigned) y)
				i = table->subtables[i].next;
			table->subtables[i].next = gxtop;
			move = (Move *)cuddDynamicAllocNode(table);
			if (move == NULL) goto ddGroupSiftingUpOutOfMem;
			move->x = x;
			move->y = y;
			move->flags = MTR_NEWNODE;
			move->size = (int) (table->keys - table->isolated);
			move->next = *moves;
			*moves = move;
		} else if (table->subtables[x].next == (unsigned) x &&
		table->subtables[y].next == (unsigned) y) {
			/* x and y are self groups */
			xindex = table->invperm[x];
			size = BkfddSwapInPlace(table,x,y);
#ifdef DD_DEBUG
			assert(table->subtables[x].next == (unsigned) x);
			assert(table->subtables[y].next == (unsigned) y);
#endif
			if (size == 0) goto ddGroupSiftingUpOutOfMem;

			/* Update the lower bound. */
			if (cuddTestInteract(table,xindex,yindex)) {
				isolated = Cudd_Regular(table->vars[xindex])->ref == 1;
				L += table->subtables[y].keys - isolated;
			}
			move = (Move *)cuddDynamicAllocNode(table);
			if (move == NULL) goto ddGroupSiftingUpOutOfMem;
			move->x = x;
			move->y = y;
			move->flags = MTR_DEFAULT;
			move->size = size;
			move->next = *moves;
			*moves = move;

#ifdef DD_DEBUG
			if (table->enableExtraDebug > 0)
				(void) fprintf(table->out,
         "ddGroupSiftingUp (2 single groups):\n");
#endif	
			if ((double) size > (double) limitSize * table->maxGrowth)
				return(1);
			if (size < limitSize) limitSize = size;
		} else { /* Group move */
			size = ddGroupMove(table,x,y,moves);
			if (size == 0) goto ddGroupSiftingUpOutOfMem;
			/* Update the lower bound. */
			z = (*moves)->y;
			do {
				zindex = table->invperm[z];
				if (cuddTestInteract(table,zindex,yindex)) {
					isolated = Cudd_Regular(table->vars[zindex])->ref == 1;
					L += table->subtables[z].keys - isolated;
				}
				z = table->subtables[z].next;
			} while (z != (int) (*moves)->y);
			if ((double) size > (double) limitSize * table->maxGrowth)
				return(1);
			if (size < limitSize) limitSize = size;
		}
		y = gxtop;
		x = cuddNextLow(table,y);
	}

	return(1);

ddGroupSiftingUpOutOfMem:
	while (*moves != NULL) {
		move = (*moves)->next;
		cuddDeallocMove(table, *moves);
		*moves = move;
	}
	return(0);

} /* end of ddGroupSiftingUp */


/**
  @brief Sifts down a variable until it reaches position xHigh.

  @details Assumes that x is the bottom of a group (or a singleton).
  Records all the moves.

  @return 1 in case of success; 0 otherwise.

  @sideeffect None

*/
static int
ddGroupSiftingDown(
  DdManager * table,
  int  x,
  int  xHigh,
  BKFDD_CHKFP checkFunction,
  Move ** moves)
{
  Move *move;
  int  y;
  int  size;
  int  limitSize;
  int  gxtop,gybot;
  int  R;	/* upper bound on node decrease */
  int  xindex, yindex;
  unsigned isolated;
  int  allVars;
  int  z;
  int  zindex;

#ifdef DD_DEBUG
  int  checkR;
#endif

	/* If the group consists of simple variables, there is no point in
	** sifting it down. This check is redundant if the projection functions
	** do not have external references, because the computation of the
	** lower bound takes care of the problem.  It is necessary otherwise to
	** prevent the sifting down of simple variables. */
	y = x;
	allVars = 1;
	do {
		if (table->subtables[y].keys != 1) {
			allVars = 0;
			break;
		}
		y = table->subtables[y].next;
	} while (table->subtables[y].next != (unsigned) x);
	if (allVars)
		return(1);

	/* Initialize R. */
	xindex = table->invperm[x];
	gxtop = table->subtables[x].next;

	assert(x >= gxtop); // x is bottom of group

	limitSize = size = (int) (table->keys - table->isolated);
	R = 0;
	for (z = xHigh; z > gxtop; z--) {
		zindex = table->invperm[z];
		if (zindex == xindex || cuddTestInteract(table,xindex,zindex)) {
			isolated = Cudd_Regular(table->vars[zindex])->ref == 1;
			R += table->subtables[z].keys - isolated;
		}
	}

	y = cuddNextHigh(table,x);
	while (y <= xHigh && size - R < limitSize) {
#ifdef DD_DEBUG
		gxtop = table->subtables[x].next;
		checkR = 0;
		for (z = xHigh; z > gxtop; z--) {
			zindex = table->invperm[z];
			if (zindex == xindex || cuddTestInteract(table,xindex,zindex)) {
				isolated = Cudd_Regular(table->vars[zindex])->ref == 1;
				checkR += table->subtables[z].keys - isolated;
			}
		}
		assert(R >= checkR);
#endif
		/* Find bottom of y group. */
		gybot = table->subtables[y].next;
		while (table->subtables[gybot].next != (unsigned) y)
			gybot = table->subtables[gybot].next;

		if (checkFunction(table,x,y)) {
			/* Group found: attach groups and record move. */
			gxtop = table->subtables[x].next;
			table->subtables[x].next = y;
			table->subtables[gybot].next = gxtop;
			move = (Move *)cuddDynamicAllocNode(table);
			if (move == NULL) goto ddGroupSiftingDownOutOfMem;
			move->x = x;
			move->y = y;
			move->flags = MTR_NEWNODE;
			move->size = (int) (table->keys - table->isolated);
			move->next = *moves;
			*moves = move;
		} else if (table->subtables[x].next == (unsigned) x &&
			table->subtables[y].next == (unsigned) y) {
			/* x and y are self groups */
			/* Update upper bound on node decrease. */
			yindex = table->invperm[y];
			if (cuddTestInteract(table,xindex,yindex)) {
				isolated = Cudd_Regular(table->vars[yindex])->ref == 1;
				R -= table->subtables[y].keys - isolated;
			}
			size = BkfddSwapInPlace(table,x,y);
#ifdef DD_DEBUG
			assert(table->subtables[x].next == (unsigned) x);
			assert(table->subtables[y].next == (unsigned) y);
#endif
			if (size == 0) goto ddGroupSiftingDownOutOfMem;

			/* Record move. */
			move = (Move *) cuddDynamicAllocNode(table);
			if (move == NULL) goto ddGroupSiftingDownOutOfMem;
			move->x = x;
			move->y = y;
			move->flags = MTR_DEFAULT;
			move->size = size;
			move->next = *moves;
			*moves = move;

#ifdef DD_DEBUG
			if (table->enableExtraDebug > 0)
				(void) fprintf(table->out,
				"ddGroupSiftingDown (2 single groups):\n");
#endif
			if ((double) size > (double) limitSize * table->maxGrowth)
				return(1);
			if (size < limitSize) limitSize = size;

		} else { /* Group move */
			/* Update upper bound on node decrease: first phase. */
			gxtop = table->subtables[x].next;
			z = gxtop + 1;
			do {
				zindex = table->invperm[z];
				if (zindex == xindex || cuddTestInteract(table,xindex,zindex)) {
					isolated = Cudd_Regular(table->vars[zindex])->ref == 1;
					R -= table->subtables[z].keys - isolated;
				}
				z++;
			} while (z <= gybot);
			size = ddGroupMove(table,x,y,moves);
			if (size == 0) goto ddGroupSiftingDownOutOfMem;

			if ((double) size > (double) limitSize * table->maxGrowth)
				return(1);
			if (size < limitSize) limitSize = size;

			/* Update upper bound on node decrease: second phase. */
			gxtop = table->subtables[gybot].next;
			for (z = gxtop + 1; z <= gybot; z++) {
				zindex = table->invperm[z];
				if (zindex == xindex || cuddTestInteract(table,xindex,zindex)) {
					isolated = Cudd_Regular(table->vars[zindex])->ref == 1;
					R += table->subtables[z].keys - isolated;
				}
			}
		}
		x = gybot;
		y = cuddNextHigh(table,x);
	}

	return(1);

ddGroupSiftingDownOutOfMem:
	while (*moves != NULL) {
		move = (*moves)->next;
		cuddDeallocMove(table, *moves);
		*moves = move;
	}

	return(0);

} /* end of ddGroupSiftingDown */


/**
  @brief Swaps two groups and records the move.

  @return the number of keys in the %DD table in case of success; 0
  otherwise.

  @sideeffect None

*/
static int
ddGroupMove(
  DdManager * table,
  int  x,
  int  y,
  Move ** moves)
{
  Move *move;
  int  size;
  int  i,j,xtop,xbot,xsize,ytop,ybot,ysize,newxtop;
  int  swapx = 0, swapy = 0;

#if defined(DD_DEBUG) && defined(DD_VERBOSE)
  int  initialSize,bestSize;
#endif

#ifdef DD_DEBUG
  /* We assume that x < y */
  assert(x < y);
#endif
	/* Find top, bottom, and size for the two groups. */
	xbot = x;
	xtop = table->subtables[x].next;
	xsize = xbot - xtop + 1;
	assert(xtop <= xbot);

	ybot = y;
	while ((unsigned) ybot < table->subtables[ybot].next)
		ybot = table->subtables[ybot].next;
	ytop = y;
	ysize = ybot - ytop + 1;
	assert(ytop <= ybot);

#if defined(DD_DEBUG) && defined(DD_VERBOSE)
	initialSize = bestSize = table->keys - table->isolated;
#endif
	/* Sift the variables of the second group up through the first group */
	for (i = 1; i <= ysize; i++) {
		for (j = 1; j <= xsize; j++) {
			size = BkfddSwapInPlace(table,x,y);
			if (size == 0) goto ddGroupMoveOutOfMem;
#if defined(DD_DEBUG) && defined(DD_VERBOSE)
			if (size < bestSize) bestSize = size;
#endif
			swapx = x; swapy = y;
			y = x;
			x = cuddNextLow(table,y);
		}
		y = ytop + i;
		x = cuddNextLow(table,y);
	}
#if defined(DD_DEBUG) && defined(DD_VERBOSE)
	if ((bestSize < initialSize) && (bestSize < size))
		(void) fprintf(table->out,"Missed local minimum: initialSize:%d  bestSize:%d  finalSize:%d\n",initialSize,bestSize,size);
#endif

	/* fix groups */
	y = xtop; /* ytop is now where xtop used to be */
	for (i = 0; i < ysize - 1; i++) {
		table->subtables[y].next = cuddNextHigh(table,y);
		y = cuddNextHigh(table,y);
	}
	table->subtables[y].next = xtop; /* y is bottom of its group, join it to top of its group */
	x = cuddNextHigh(table,y);
	newxtop = x;
	for (i = 0; i < xsize - 1; i++) {
		table->subtables[x].next = cuddNextHigh(table,x);
		x = cuddNextHigh(table,x);
	}
	table->subtables[x].next = newxtop; /* x is bottom of its group, join it to top of its group */
#ifdef DD_DEBUG
	if (table->enableExtraDebug > 0)
		(void) fprintf(table->out,"ddGroupMove:\n");
#endif

	/* Store group move */
	move = (Move *) cuddDynamicAllocNode(table);
	if (move == NULL) goto ddGroupMoveOutOfMem;
	move->x = swapx;
	move->y = swapy;
	move->flags = MTR_DEFAULT;
	move->size = (int) (table->keys - table->isolated);
	move->next = *moves;
	*moves = move;

	return((int)(table->keys - table->isolated));

ddGroupMoveOutOfMem:
	while (*moves != NULL) {
		move = (*moves)->next;
		cuddDeallocMove(table, *moves);
		*moves = move;
	}
	return(0);

} /* end of ddGroupMove */


/**
  @brief Undoes the swap two groups.

  @return 1 in case of success; 0 otherwise.

  @sideeffect None

*/
static int
ddGroupMoveBackward(
  DdManager * table,
  int  x,
  int  y)
{
  int size;
  int i,j,xtop,xbot,xsize,ytop,ybot,ysize,newxtop;

#ifdef DD_DEBUG
  /* We assume that x < y */
  assert(x < y);
#endif

	/* Find top, bottom, and size for the two groups. */
	xbot = x;
	xtop = table->subtables[x].next;
	xsize = xbot - xtop + 1;
	ybot = y;
	while ((unsigned) ybot < table->subtables[ybot].next)
		ybot = table->subtables[ybot].next;
	ytop = y;
	ysize = ybot - ytop + 1;

	/* Sift the variables of the second group up through the first group */
	for (i = 1; i <= ysize; i++) {
		for (j = 1; j <= xsize; j++) {
			size = BkfddSwapInPlace(table,x,y);
			if (size == 0) return(0);

			y = x;
			x = cuddNextLow(table,y);
		}
		y = ytop + i;
		x = cuddNextLow(table,y);
	}

	/* fix groups */
	y = xtop;
	for (i = 0; i < ysize - 1; i++) {
		table->subtables[y].next = cuddNextHigh(table,y);
		y = cuddNextHigh(table,y);
	}
	table->subtables[y].next = xtop; /* y is bottom of its group, join to its top */
	x = cuddNextHigh(table,y);
	newxtop = x;
	for (i = 0; i < xsize - 1; i++) {
		table->subtables[x].next = cuddNextHigh(table,x);
		x = cuddNextHigh(table,x);
	}
	table->subtables[x].next = newxtop; /* x is bottom of its group, join to its top */

#ifdef DD_DEBUG
	if (table->enableExtraDebug > 0)
		(void) fprintf(table->out,"ddGroupMoveBackward:\n");
#endif

	return(1);

} /* end of ddGroupMoveBackward */


/**
  @brief Determines the best position for a variables and returns
  it there.

  @return 1 in case of success; 0 otherwise.

  @sideeffect None

*/
static int
ddGroupSiftingBackward(
  DdManager * table,
  Move * moves,
  int  size)
{
  Move *move;
  int  res;

	/* Find the minimum size. */
	for (move = moves; move != NULL; move = move->next) {
		if (move->size < size) {
			size = move->size;
		}
	}

	/* We stop as soon as we meet
	 the minimum size. */
	for (move = moves; move != NULL; move = move->next) {
		if (move->size == size) return(1);
		if ((table->subtables[move->x].next == move->x) &&
		(table->subtables[move->y].next == move->y)) {
			res = BkfddSwapInPlace(table,(int)move->x,(int)move->y);
			if (!res) return(0);

#ifdef DD_DEBUG	
			if (table->enableExtraDebug > 0)
			(void) fprintf(table->out,"ddGroupSiftingBackward:\n");
			assert(table->subtables[move->x].next == move->x);
			assert(table->subtables[move->y].next == move->y);
#endif	
		} else { /* Group move necessary */
			if (move->flags == MTR_NEWNODE) {
				ddDissolveGroup(table,(int)move->x,(int)move->y);
			} else {
				res = ddGroupMoveBackward(table,(int)move->x,(int)move->y);
				if (!res) return(0);
			}
		}
	}

	return(1);

} /* end of ddGroupSiftingBackward */


/**
  @brief Dissolves a group in the %DD table.

  @details x and y are variables in a group to be cut in two. The cut
  is to pass between x and y.

  @sideeffect None

	@NOTE Xuanxiang Huang: make sure biconditional groups are not be dissolve

*/
static void
ddDissolveGroup(
  DdManager * table,
  int  x,
  int  y)
{
	int topx;
	int boty;
	int xdec = table->expansion[x];
	int ydec = table->expansion[y];
	/* Bi-Bi or Bi-Cla means x and y are in the same biconditional group,
		which cannot be dissolved. */
	assert( (isCla(xdec) && isCla(ydec)) || 
					(isCla(xdec) && isBi(ydec)) );
	/* find top and bottom of the two groups */
	boty = y;
	while ((unsigned) boty < table->subtables[boty].next)
		boty = table->subtables[boty].next;

	topx = table->subtables[boty].next;

	table->subtables[boty].next = y;
	table->subtables[x].next = topx;

	return;

} /* end of ddDissolveGroup */


/**
  @brief Pretends to check two variables for aggregation.

  @return always 0.

  @sideeffect None

*/
static int
ddNoCheck(
  DdManager * table,
  int  x,
  int  y)
{
  (void) table; /* avoid warning */
  (void) x;     /* avoid warning */
  (void) y;     /* avoid warning */
  return(0);

} /* end of ddNoCheck */


/**
  @brief Checks two variables for aggregation.

  @details The check is based on the second difference of the number
  of nodes as a function of the layer. If the second difference is
  lower than a given threshold (typically negative) then the two
  variables should be aggregated.

  @return 1 if the two variables pass the test; 0 otherwise.

  @sideeffect None

*/
static int
ddSecDiffCheck(
  DdManager * table,
  int  x,
  int  y)
{
  double Nx,Nx_1;
  double Sx;
  double threshold;
  int    xindex,yindex;

  if (x==0) return(0);

#ifdef DD_STATS
	table->secdiffcalls++;
#endif
	Nx = (double) table->subtables[x].keys;
	Nx_1 = (double) table->subtables[x-1].keys;
	Sx = (table->subtables[y].keys/Nx) - (Nx/Nx_1);

	threshold = table->recomb / 100.0;
	if (Sx < threshold) {
		xindex = table->invperm[x];
		yindex = table->invperm[y];
		if (cuddTestInteract(table,xindex,yindex)) {
#if defined(DD_DEBUG) && defined(DD_VERBOSE)
			(void) fprintf(table->out,
			"Second difference for %d = %g Pos(%d)\n",
			table->invperm[x],Sx,x);
#endif
#ifdef DD_STATS
			table->secdiff++;
#endif
			return(1);
		} else {
#ifdef DD_STATS	
			table->secdiffmisfire++;
#endif
			return(0);
		}

	}
	return(0);

} /* end of ddSecDiffCheck */


/** @brief get OET information */
static void
getOET(
	DdManager * table,
	Oet * oet)
{
	int nvars = table->size;
	int i, idx;
	// get OET information
	for (i = 0; i < nvars; i ++) { // i is level
		idx = table->invperm[i]; // primary variable index of i-level
		oet[idx].expn = table->expansion[i];
		if (isBi(table->expansion[i])) {
			oet[idx].sv = table->invperm[i+1];
			oet[idx].nextIdx = table->invperm[i+1];
		} else {
			oet[idx].sv = -1;
			oet[idx].nextIdx = -1;
		}
		oet[idx].top_mid_bot = -1;
	}
	int count = 0;
	for (i = 0; i < nvars; i ++) { // i is level
		if (isBi(table->expansion[i])) {
			int top = i; // top level of group
			while (isBi(table->expansion[i])) {
				idx = table->invperm[i];
				oet[idx].top_mid_bot = G_MID;
				i ++;
				count ++;
			}
			// get bottom variable of group
			assert(isCla(table->expansion[i]));
			idx = table->invperm[i];
			oet[idx].nextIdx = table->invperm[top];
			oet[idx].top_mid_bot = G_BOT;
			oet[table->invperm[top]].top_mid_bot = G_TOP;
		}
		count ++;
	}
	assert(count == nvars);
	return;
} /* end of getOET */


/** 
	@brief Compare two oet information. 
		
	@detail return 1 if two oet identical, otherwise 0;
	
*/
static int
oetCompare(
	DdManager * table)
{
	int nvars = table->size;
	int i, k, idx, topidx;
	/* group of two OET must identical, during reordering,
	only variable order changed, expansion which assocated
	with variable don't change. */
	for (i = 0; i < nvars; i ++) { // i is level
		if (isBi(table->expansion[i])) {
			/* find top of biconditional group in oet1, and check,
				we don't have level information of oet1.
			*/
			topidx = table->invperm[i]; // get top variable of biconditional group in oet2
			if (table->oet2[topidx].top_mid_bot != G_TOP) {
				printf("oetCompare[Bi]: pv%d is not top of group\n", topidx);
				goto oetCompareError;
			}
			if (table->oet2[topidx].top_mid_bot != table->oet1[topidx].top_mid_bot) {
				printf("oetCompare[Bi]: top pv%d in wrong position of group\n", topidx);
				goto oetCompareError;
			}
			if (table->oet2[topidx].sv != table->oet1[topidx].sv) {
				printf("oetCompare[Bi]: sv of top pv%d not same\n", topidx);
				goto oetCompareError;
			}
			if (isCla(table->oet2[topidx].expn)) {
				printf("oetCompare[Bi]: invalid expn of top pv%d\n", topidx);
				goto oetCompareError;
			}
			if (table->oet2[topidx].expn != table->oet1[topidx].expn) {
				printf("oetCompare[Bi]: expn of top pv%d not same\n", topidx);
				goto oetCompareError;
			}
			if (table->oet2[topidx].nextIdx != table->oet1[topidx].nextIdx) {
				printf("oetCompare[Bi]: group of top pv%d not same\n", topidx);
			}
			assert(table->oet2[topidx].sv == table->oet2[topidx].nextIdx);
			assert(table->invperm[i+1] == table->oet2[topidx].nextIdx);
			i ++;
			// check middle of group
			while (isBi(table->expansion[i])) {
				idx = table->invperm[i];
				if (table->oet2[idx].sv != table->oet1[idx].sv) {
					printf("oetCompare[Bi]: sv of middle pv%d not same\n",idx);
					goto oetCompareError;
				}
				if (isCla(table->oet2[idx].expn)) {
					printf("oetCompare[Bi]: classical expn contained in middle of group, pv%d\n",idx);
					goto oetCompareError;
				}
				if (table->oet2[idx].expn != table->oet1[idx].expn) {
					printf("oetCompare[Bi]: expn of middle pv%d not same\n",idx);
					goto oetCompareError;
				}
				if (table->oet2[idx].top_mid_bot != G_MID) {
					printf("oetCompare[Bi]: wrong position of middle pv%d\n", idx);
					goto oetCompareError;
				}
				if (table->oet2[idx].top_mid_bot != table->oet1[idx].top_mid_bot) {
					printf("oetCompare[Bi]: position of middle pv%d not same\n",idx);
					goto oetCompareError;
				}
				if (table->oet2[idx].nextIdx != table->oet1[idx].nextIdx) {
					printf("oetCompare[Bi]: next idx of middle pv%d not same\n", idx);
				}
				assert(table->oet2[idx].sv == table->oet2[idx].nextIdx);
				assert(table->invperm[i+1] == table->oet2[idx].nextIdx);
				i ++;
			}
			// reach bottom of biconditional group
			idx = table->invperm[i];
			if (isBi(table->oet2[idx].expn)) {
				printf("oetCompare[Bi]: invalid expn for bottom pv%d\n", idx);
				goto oetCompareError;
			}
			assert(table->oet2[idx].sv == -1);
			if (table->oet2[idx].sv != table->oet1[idx].sv) {
				printf("oetCompare[Bi]: sv of bottom pv%d not same\n",idx);
				goto oetCompareError;
			}
			if (table->oet2[idx].expn != table->oet1[idx].expn) {
				printf("oetCompare[Bi]: expn of bottom pv%d not same\n",idx);
				goto oetCompareError;
			}
			if (table->oet2[idx].top_mid_bot != G_BOT) {
				printf("oetCompare[Bi]: bottom pv%d in wrong position\n", idx);
				goto oetCompareError;
			}
			if (table->oet2[idx].top_mid_bot != table->oet1[idx].top_mid_bot) {
				printf("oetCompare[Bi]: bottom pv%d in different position\n",idx);
				goto oetCompareError;
			}
			if (table->oet2[idx].nextIdx != topidx) {
				printf("oetCompare[Bi]: next idx of bottom pv%d is not top of group\n", idx);
				goto oetCompareError;
			}
			if (table->oet2[idx].nextIdx != table->oet1[idx].nextIdx) {
				printf("oetCompare[Bi]: next idx of bottom pv%d not same\n", idx);
				goto oetCompareError;
			}
		} else {
			// single variable group
			idx = table->invperm[i];
			assert(table->oet2[idx].sv == -1);
			assert(table->oet2[idx].sv == table->oet2[idx].nextIdx);
			if (isBi(table->oet2[idx].expn)) {
				printf("oetCompare[Single]: invalid expn of pv%d\n",idx);
				goto oetCompareError;
			}
			if (table->oet2[idx].sv != table->oet1[idx].sv) {
				printf("oetCompare[Single]: sv of pv%d not same\n",idx);
				goto oetCompareError;
			}
			if (table->oet2[idx].expn != table->oet1[idx].expn) {
				printf("oetCompare[Single]: expn of pv%d not same\n",idx);
				goto oetCompareError;
			}
			assert(table->oet2[idx].top_mid_bot == -1);
			if (table->oet2[idx].top_mid_bot != table->oet1[idx].top_mid_bot) {
				printf("oetCompare[Single]: pv%d contained in some group\n",idx);
				goto oetCompareError;
			}
			assert(table->oet2[idx].nextIdx == -1);
			if (table->oet2[idx].nextIdx != table->oet1[idx].nextIdx) {
				printf("oetCompare[Single]: next index of pv%d not same\n",idx);
				goto oetCompareError;
			}
		}
	}
	return(1);
oetCompareError:
	printf("OET:\n");
	for (k = 0; k < nvars; k ++) { // k is level
		idx = table->invperm[k]; // get variable index of oet2
		printf("lvl-%d: [oet2](pv%d,sv%d)[expn%d]{next:%d}@%d   [oet1](pv%d,sv%d)[expn%d]{next:%d}@%d\n"
		,k,idx,table->oet2[idx].sv,table->oet2[idx].expn,
		table->oet2[idx].nextIdx,table->oet2[idx].top_mid_bot,
		idx,table->oet1[idx].sv,table->oet1[idx].expn,
		table->oet2[idx].nextIdx,table->oet2[idx].top_mid_bot);
	}
	printf("END of OET\n");

	return(0);
} /* end of oetCompare */

#if 0
/** 
	@brief check identity of biconditional group information
	contained in OET and subtables.

	@NOTE we assume oet is valid(has been checked). So we
	only need to check group member of each group.

*/
static int
checkBiGroup(
	DdManager * table,
	Oet * oet)
{
	int i;
	int idx;
	for (i = 0; i < table->size; i ++) {
		if (isBi(table->expansion[i])) { // biconditional group
			// get top of biconditional group
			int toplvl = i;
			int topidx = table->invperm[toplvl];
			if (oet[topidx].top_mid_bot != G_TOP) {
				printf("checkBiGroup[Bi]: group inconsistent at top pv%d\n", topidx);
				return(0);
			}
			if ((unsigned)(table->perm[oet[topidx].nextIdx]) != table->subtables[toplvl].next) {
				printf("checkBiGroup[Bi]: next group member of top pv%d not same\n", topidx);
				return(0);
			}
			i ++;
			// middle of biconditional group
			while (isBi(table->expansion[i])) {
				idx = table->invperm[i];
				if (oet[idx].top_mid_bot != G_MID) {
					printf("checkBiGroup[Bi]: group inconsistent at middle pv%d\n", idx);
					return(0);
				}
				if ((unsigned)(table->perm[oet[idx].nextIdx]) != table->subtables[i].next) {
					printf("checkBiGroup[Bi]: next group member of middle pv%d not same\n", idx);
					return(0);						
				}
				i ++;
			}
			// reach bottom of group
			assert(isCla(table->expansion[i]));
			idx = table->invperm[i];
			if (oet[idx].top_mid_bot != G_BOT) {
				printf("checkBiGroup[Bi]: group inconsistent at bottom pv%d\n", idx);
				return(0);
			}
			if (table->subtables[i].next != (unsigned)toplvl) {
				printf("checkBiGroup[Bi]: groups in subtables invalid, at bottom pv%d\n", idx);
				return(0);
			}
			if (table->perm[oet[idx].nextIdx] != toplvl) {
				printf("checkBiGroup[Bi]: next group member of bottom pv%d is not top\n", idx);
				return(0);
			}
		} else { // single variable group or classical group
			/* in oet, all variables assocatied wich classical expansions
				are treated as single variable group */
			if (table->subtables[i].next != (unsigned)i) {
				/* treated as classical group in bkfddgroupsifting,
					make sure there is no biconditional group contained. */
				int init = i;
				do {
					idx = table->invperm[i];
					if ( (oet[idx].sv != -1) ||
							isBi(oet[idx].expn) ||
							(oet[idx].top_mid_bot != -1) ||
							(oet[idx].nextIdx != -1)	) {
						printf("checkBiGroup[Cla]: error in classical group, at pv%d\n", idx);
						return(0);
					}
					i = table->subtables[i].next;
				} while (i != init);
			} else { // single variable group
				idx = table->invperm[i];
				if ( (oet[idx].sv != -1) ||
						isBi(oet[idx].expn) ||
						(oet[idx].top_mid_bot != -1) ||
						(oet[idx].nextIdx != -1)	) {
					printf("checkBiGroup[Cla]: error in classical group, at pv%d\n", idx);
					return(0);
				}
			}
		}
	}
	return(1);
} /* end of checkBiGroup*/
#endif

/**
  @brief Checks for symmetry of x and y in BKFDD.
	@details
		1. for two adjacent S-S level:
				(f11 == f00) || (f10 == f01)
		2. for two adjacent S-D level:
					(f11 \xor f01 == f10) || (f11 \xor f01 == f00)
		3. for two adjacent D-S level:
					(f11 \xor f10 == f01) || (f11 \xor f10 == f00)
		4. for two adjacent D-D leve:
					(f10 == f01) || (f10 \xor f01 == f00)

	For practical reason, we only use S-S check condition.
	(f11 == f00) || (f10 == f01)

  @return 1 in case of extended symmetry; 0 otherwise.

  @sideeffect None

*/
static int
bkfddSymmCheck(
  DdManager * table,
  int  x,
  int  y)
{
  DdNode *f,*f0,*f1,*f01,*f00,*f11,*f10;
  DdNode *one, *zero;
  int comple;		/* f0 is complemented */
  int notproj;	/* f is not a projection function */
  int arccount;	/* number of arcs from layer x to layer y */
  int TotalRefCount;	/* total reference count of layer y minus 1 */
  int i;
  int xindex;
  int yindex;
  int slots;
	int xdec, ydec;
  DdNodePtr *list;
  DdNode *sentinel = &(table->sentinel);

  xindex = table->invperm[x];
  yindex = table->invperm[y];
	xdec = table->expansion[x];
	ydec = table->expansion[y];
	
	/* Bi-Bi or Bi-Cla means x,y already be merged. */
	assert( (isCla(xdec) && isCla(ydec)) ||
					(isCla(xdec) && isBi(ydec)) );

	if ((isCla(xdec) && isBi(ydec)))
		return(0);

	/* If the two variables do not interact, we do not want to merge them. */
	if (!cuddTestInteract(table,xindex,yindex)) {
		return(0);
	}

#ifdef DD_DEBUG
	/* Checks that x and y do not contain just the projection functions.
	** With the test on interaction, these test become redundant,
	** because an isolated projection function does not interact with
	** any other variable.
	*/
	if (table->subtables[x].keys == 1) {
		assert(Cudd_Regular(table->vars[xindex])->ref != 1);
	}
	if (table->subtables[y].keys == 1) {
		assert(Cudd_Regular(table->vars[yindex])->ref != 1);
	}
#endif

#ifdef DD_STATS
  table->extsymmcalls++;
#endif
	
	// possible symmetry type
	int symtype;
	if (isShan(xdec)) {
		if (isShan(ydec)) {
			symtype = S_S_SYM;
		} else {
			symtype = S_D_SYM;
			return(0);
		}
	} else {
		if (isShan(ydec)) {
			symtype = D_S_SYM;
			return(0);
		} else {
			symtype = D_D_SYM;
		}
	}

	arccount = 0;	

	one = DD_ONE(table);
	zero = Cudd_Not(one);

	slots = table->subtables[x].slots;
	list = table->subtables[x].nodelist;
	for (i = 0; i < slots; i++) {
		f = list[i];
		while (f != sentinel) {
			/* Find f1, f0, f11, f10, f01, f00. */
			f1 = cuddT(f);
			f0 = Cudd_Regular(cuddE(f));
			comple = Cudd_IsComplement(cuddE(f));
			notproj = f1 != one || f0 != one || f->ref != (DdHalfWord) 1;
			if (f1->index == (unsigned) yindex) {
				arccount++;
				f11 = cuddT(f1); f10 = cuddE(f1);
			} else { // f1->index != yindex
				if ((int) f0->index != yindex) {
					/* If f is an isolated projection function it is
					** allowed to bypass layer y.
					*/
					if (notproj) return(0);
				}
				f11 = f1;
				if (isShan(ydec)) {
					f10 = f1;	
				} else {
					f10 = zero;
				}
			}
			// f0 is regular
			if ((int) f0->index == yindex) {
				arccount++;
				f01 = cuddT(f0); f00 = cuddE(f0);
			} else {
				f01 = f0;
				if (isShan(ydec)) {
					f00 = f0;
				} else {
					f00 = zero;
				}
			}
			if (comple) {
				f01 = Cudd_Not(f01);
				if (isShan(ydec)) {
					f00 = Cudd_Not(f00);
				}
			}

			if (notproj) {
				if (symtype == S_S_SYM) {
					if ( (f11 != f00) && (f10 != f01) ) {
						return(0);
					}
				} else if (symtype == S_D_SYM) {
					if ( (f11 != f00) && (f10 != f01) ) {
						return(0);
					}
				} else if (symtype == D_S_SYM) {
					if ( (f11 != f00) && (f10 != f01) ) {
						return(0);
					}
				} else {
					if ( (f10 != f01) ) {
						return(0);
					}
				}
			}
			f = f->next;
		} /* while */
	} /* for */

	/* Calculate the total reference counts of y */
	TotalRefCount = -1;	/* -1 for projection function */
	slots = table->subtables[y].slots;
	list = table->subtables[y].nodelist;
	for (i = 0; i < slots; i++) {
		f = list[i];
		while (f != sentinel) {
			TotalRefCount += f->ref;
			f = f->next;
		}
	}


#if defined(DD_DEBUG) && defined(DD_VERBOSE)
	if (arccount == TotalRefCount) {
		xindex = table->invperm[x];
		(void) fprintf(table->out,
		"Found symmetry! x =%d\ty = %d\tPos(%d,%d)\n",
		xindex,yindex,x,y);
	}
#endif

	return(arccount == TotalRefCount);

} /* end of bkfddSymmCheck */


/**
  @brief Checks for symmetry of x and y in BKFDD.
	@details
		1. for two adjacent S-S level:
				(f11 == f00) || (f10 == f01)
		2. for two adjacent S-D level:
					(f11 \xor f01 == f10) || (f11 \xor f01 == f00)
		3. for two adjacent D-S level:
					(f11 \xor f10 == f01) || (f11 \xor f10 == f00)
		4. for two adjacent D-D leve:
					(f10 == f01) || (f10 \xor f01 == f00)

  @return 1 in case of extended symmetry; 0 otherwise.

  @sideeffect None

*/
int
bkfddExtSymmCheck1(
  DdManager * table,
  int  x,
  int  y)
{
  DdNode *f,*f0,*f1,*f01,*f00,*f11,*f10,*tmp;
  DdNode *one, *zero;
  int comple;		/* f0 is complemented */
  int notproj;	/* f is not a projection function */
  int arccount;	/* number of arcs from layer x to layer y */
  int TotalRefCount;	/* total reference count of layer y minus 1 */
  int counter;	/* number of nodes of layer x that are allowed */
								/* to violate extended symmetry conditions */
  int arccounter;	/* number of arcs into layer y that are allowed */
									/* to come from layers other than x */
  int i;
  int xindex;
  int yindex;
  int res;
  int slots;
	int xdec, ydec;
  DdNodePtr *list;
  DdNode *sentinel = &(table->sentinel);
	unsigned int keys1, iso1;

  xindex = table->invperm[x];
  yindex = table->invperm[y];
	xdec = table->expansion[x];
	ydec = table->expansion[y];
	
	/* Bi-Bi or Bi-Cla means x,y already be merged. */
	assert( (isCla(xdec) && isCla(ydec)) ||
					(isCla(xdec) && isBi(ydec)) );

	/* If the two variables do not interact, we do not want to merge them. */
	if (!cuddTestInteract(table,xindex,yindex)) {
		return(0);
	}

#ifdef DD_DEBUG
	/* Checks that x and y do not contain just the projection functions.
	** With the test on interaction, these test become redundant,
	** because an isolated projection function does not interact with
	** any other variable.
	*/
	if (table->subtables[x].keys == 1) {
		assert(Cudd_Regular(table->vars[xindex])->ref != 1);
	}
	if (table->subtables[y].keys == 1) {
		assert(Cudd_Regular(table->vars[yindex])->ref != 1);
	}
#endif

#ifdef DD_STATS
  table->extsymmcalls++;
#endif

	// possible symmetry type
	int symtype;
	if (isShan(xdec)) {
		if (isShan(ydec)) {
			symtype = S_S_SYM;
		} else {
			symtype = S_D_SYM;
		}
	} else {
		if (isShan(ydec)) {
			symtype = D_S_SYM;
		} else {
			symtype = D_D_SYM;
		}
	}

	if (symtype != S_S_SYM) {
		garbageCollectSimple(table,x);
	}

	arccount = 0;

	counter = (int) (table->subtables[x].keys *
	(table->symmviolation/100.0) + 0.5);

	one = DD_ONE(table);
	zero = Cudd_Not(one);

	int cleanMark = 0;

	keys1 = table->keys;
	iso1 = table->isolated;

	slots = table->subtables[x].slots;
	list = table->subtables[x].nodelist;
	for (i = 0; i < slots; i++) {
		f = list[i];
		while (f != sentinel) {
			/* Find f1, f0, f11, f10, f01, f00. */
			f1 = cuddT(f);
			f0 = Cudd_Regular(cuddE(f));
			comple = Cudd_IsComplement(cuddE(f));
			notproj = f1 != one || f0 != one || f->ref != (DdHalfWord) 1;
			if (f1->index == (unsigned) yindex) {
				arccount++;
				f11 = cuddT(f1); f10 = cuddE(f1);
			} else { // f1->index != yindex
				if ((int) f0->index != yindex) {
					/* If f is an isolated projection function it is
					** allowed to bypass layer y.
					*/
					if (notproj) {
						if (counter == 0)
						return(0);
						counter--; /* f bypasses layer y */
					}
				}
				f11 = f1;
				if (isShan(ydec)) {
					f10 = f1;	
				} else {
					f10 = zero;
				}
			}
			// f0 is regular
			if ((int) f0->index == yindex) {
				arccount++;
				f01 = cuddT(f0); f00 = cuddE(f0);
			} else {
				f01 = f0;
				if (isShan(ydec)) {
					f00 = f0;
				} else {
					f00 = zero;
				}
			}
			if (comple) {
				f01 = Cudd_Not(f01);
				if (isShan(ydec)) {
					f00 = Cudd_Not(f00);
				}
			}

			if (notproj) {
				if (symtype == S_S_SYM) {
					if ( (f11 != f00) && (f10 != f01) ) {
						if (counter == 0) {
							return(0);
						}
						counter --;
					}
				} else if (symtype == S_D_SYM) {
					tmp = BkfddXorRecur_Inner(table,f11,f01);
					assert(tmp != NULL);
					if ( (tmp != f10) && (tmp != f00) ) {
						cleanMark = 1;
						if (counter == 0) {
							garbageCollectSimple(table,x);
							assert(iso1 == table->isolated);
							assert(keys1 == table->keys);
							return(0);
						}
						counter --;
					}
				} else if (symtype == D_S_SYM) {
					tmp = BkfddXorRecur_Inner(table,f11,f10);
					assert(tmp != NULL);
					if ( (tmp != f01) && (tmp != f00) ) {
						cleanMark = 1;
						if (counter == 0) {
							garbageCollectSimple(table,x);
							assert(iso1 == table->isolated);
							assert(keys1 == table->keys);
							return(0);
						}
						counter --;
					}
				} else {
					if (f10 != f01) {
						tmp = BkfddXorRecur_Inner(table,f10,f01);
						assert(tmp != NULL);
						if (tmp != f00) {
							cleanMark = 1;
							if (counter == 0) {
								garbageCollectSimple(table,x);
								assert(iso1 == table->isolated);
								assert(keys1 == table->keys);
								return(0);
							}
							counter --;
						}
					}
				}
			}
			f = f->next;
		} /* while */
	} /* for */

	if (cleanMark) {
		garbageCollectSimple(table,x);
		assert(iso1 == table->isolated);
		assert(keys1 == table->keys);
	}

	/* Calculate the total reference counts of y */
	TotalRefCount = -1;	/* -1 for projection function */
	slots = table->subtables[y].slots;
	list = table->subtables[y].nodelist;
	for (i = 0; i < slots; i++) {
		f = list[i];
		while (f != sentinel) {
			TotalRefCount += f->ref;
			f = f->next;
		}
	}

	arccounter = (int) (table->subtables[y].keys *
	(table->arcviolation/100.0) + 0.5);

	res = arccount >= TotalRefCount - arccounter;

#if defined(DD_DEBUG) && defined(DD_VERBOSE)
	if (res) {
		(void) fprintf(table->out,
		"Found BKFDD-extended symmetry! x = %d\ty = %d\tPos(%d,%d)\n",
		xindex,yindex,x,y);
	}
#endif

#ifdef DD_STATS
	if (res)
	table->extsymm++;
#endif
	return(res);

} /* end of bkfddExtSymmCheck1 */


/**
  @brief Checks for extended symmetry of x and y in BKFDD.
	10% violation allowd.
	@details
		1. for two adjacent S-S level:
				(f11 == f00) || (f10 == f01)
		2. for two adjacent S-D level:
					(f11 \xor f01 == f10) || (f11 \xor f01 == f00)
		3. for two adjacent D-S level:
					(f11 \xor f10 == f01) || (f11 \xor f10 == f00)
		4. for two adjacent D-D leve:
					(f10 == f01) || (f10 \xor f01 == f00)

	For practical reason, we use S-S check condition for
	all four cases, it seems that the above 4 conditions
	don't suit BKFDDs.
	(f11 == f00) || (f10 == f01)

  @return 1 in case of extended symmetry; 0 otherwise.

  @sideeffect None

*/
int
bkfddExtSymmCheck2(
  DdManager * table,
  int  x,
  int  y)
{
  DdNode *f,*f0,*f1,*f01,*f00,*f11,*f10;
  DdNode *one, *zero;
  int comple;		/* f0 is complemented */
  int notproj;	/* f is not a projection function */
  int arccount;	/* number of arcs from layer x to layer y */
  int TotalRefCount;	/* total reference count of layer y minus 1 */
  int counter;	/* number of nodes of layer x that are allowed */
								/* to violate extended symmetry conditions */
  int arccounter;	/* number of arcs into layer y that are allowed */
									/* to come from layers other than x */
  int i;
  int xindex;
  int yindex;
  int res;
  int slots;
	int xdec, ydec;
  DdNodePtr *list;
  DdNode *sentinel = &(table->sentinel);

  xindex = table->invperm[x];
  yindex = table->invperm[y];
	xdec = table->expansion[x];
	ydec = table->expansion[y];
	
	/* Bi-Bi or Bi-Cla means x,y already be merged. */
	assert( (isCla(xdec) && isCla(ydec)) ||
					(isCla(xdec) && isBi(ydec)) );
	
	if ((isCla(xdec) && isBi(ydec)))
		return(0);

	/* If the two variables do not interact, we do not want to merge them. */
	if (!cuddTestInteract(table,xindex,yindex)) {
		return(0);
	}

#ifdef DD_DEBUG
	/* Checks that x and y do not contain just the projection functions.
	** With the test on interaction, these test become redundant,
	** because an isolated projection function does not interact with
	** any other variable.
	*/
	if (table->subtables[x].keys == 1) {
		assert(Cudd_Regular(table->vars[xindex])->ref != 1);
	}
	if (table->subtables[y].keys == 1) {
		assert(Cudd_Regular(table->vars[yindex])->ref != 1);
	}
#endif

#ifdef DD_STATS
  table->extsymmcalls++;
#endif
	
	// possible symmetry type
	int symtype;
	if (isShan(xdec)) {
		if (isShan(ydec)) {
			symtype = S_S_SYM;
		} else {
			symtype = S_D_SYM;
			return(0);
		}
	} else {
		if (isShan(ydec)) {
			symtype = D_S_SYM;
			return(0);
		} else {
			symtype = D_D_SYM;
		}
	}

	arccount = 0;

	counter = (int) (table->subtables[x].keys *
	(table->symmviolation/100.0) + 0.5);

	one = DD_ONE(table);
	zero = Cudd_Not(one);

	slots = table->subtables[x].slots;
	list = table->subtables[x].nodelist;
	for (i = 0; i < slots; i++) {
		f = list[i];
		while (f != sentinel) {
			/* Find f1, f0, f11, f10, f01, f00. */
			f1 = cuddT(f);
			f0 = Cudd_Regular(cuddE(f));
			comple = Cudd_IsComplement(cuddE(f));
			notproj = f1 != one || f0 != one || f->ref != (DdHalfWord) 1;
			if (f1->index == (unsigned) yindex) {
				arccount++;
				f11 = cuddT(f1); f10 = cuddE(f1);
			} else { // f1->index != yindex
				if ((int) f0->index != yindex) {
					/* If f is an isolated projection function it is
					** allowed to bypass layer y.
					*/
					if (notproj) {
						if (counter == 0)
						return(0);
						counter--; /* f bypasses layer y */
					}
				}
				f11 = f1;
				if (isShan(ydec)) {
					f10 = f1;	
				} else {
					f10 = zero;
				}
			}
			// f0 is regular
			if ((int) f0->index == yindex) {
				arccount++;
				f01 = cuddT(f0); f00 = cuddE(f0);
			} else {
				f01 = f0;
				if (isShan(ydec)) {
					f00 = f0;
				} else {
					f00 = zero;
				}
			}
			if (comple) {
				f01 = Cudd_Not(f01);
				if (isShan(ydec)) {
					f00 = Cudd_Not(f00);
				}
			}

			if (notproj) {
				if (symtype == S_S_SYM) {
					if ( (f11 != f00) && (f10 != f01) ) {
						if (counter == 0) {
							return(0);
						}
						counter --;
					}
				} else if (symtype == S_D_SYM) {
					if ( (f11 != f00) && (f10 != f01) ) {
						if (counter == 0) {
							return(0);
						}
						counter --;
					}
				} else if (symtype == D_S_SYM) {
					if ( (f11 != f00) && (f10 != f01) ) {
						if (counter == 0) {
							return(0);
						}
						counter --;
					}
				} else {
					if ( (f10 != f01) ) {
						if (counter == 0) {
							return(0);
						}
						counter --;
					}
				}
			}
			f = f->next;
		} /* while */
	} /* for */

	/* Calculate the total reference counts of y */
	TotalRefCount = -1;	/* -1 for projection function */
	slots = table->subtables[y].slots;
	list = table->subtables[y].nodelist;
	for (i = 0; i < slots; i++) {
		f = list[i];
		while (f != sentinel) {
			TotalRefCount += f->ref;
			f = f->next;
		}
	}

	arccounter = (int) (table->subtables[y].keys *
	(table->arcviolation/100.0) + 0.5);

	res = arccount >= TotalRefCount - arccounter;

#if defined(DD_DEBUG) && defined(DD_VERBOSE)
	if (res) {
		(void) fprintf(table->out,
		"Found BKFDD-extended symmetry simplified ! x = %d\ty = %d\tPos(%d,%d)\n",
		xindex,yindex,x,y);
	}
#endif

#ifdef DD_STATS
	if (res)
	table->extsymm++;
#endif
	return(res);

} /* end of bkfddExtSymmCheck2 */
