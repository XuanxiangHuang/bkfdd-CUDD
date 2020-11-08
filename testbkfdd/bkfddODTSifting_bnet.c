/**
  @file

  @ingroup bkfdd

  @brief Functions for BKFDD sifting.

	@author Xuanxiang Huang

  @copyright
  Copyright (c) 2019-, Jinan University, Guangzhou, China.

  All rights reserved.

======================================================================
	All functions are originate from cuddGroup.c

	@Modification and Extension details
		1. Add functions for sifting BKFDD, it is an extension of DTL-sifting.
		2. Add functions for swapping adjacent variables.
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
#include "cuddInt.h"
#include "bkfddInt.h"
#include "bkfdd_bnet.h"

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Stucture declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

typedef int (*DD_CHKFP)(DdManager *, int, int);
#define BACK_UP		0
#define BACK_DOWN	1

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
static int odtSiftingAux_bnet (DdManager *table, int x, int xLow, int xHigh, BnetNetwork * network);
static Move * odtSiftingUp_bnet (DdManager *table, int y, int xLow, Move *best, BnetNetwork * network);
static Move * odtSiftingDown_bnet (DdManager *table, int x, int xHigh, Move *best, BnetNetwork * network);
static int odtSiftingBackward_bnet (DdManager *table, int currentPos, Move *best, BnetNetwork * network);
static int complexSwap_bnet (DdManager * table, int x, int y, BnetNetwork * network);
static int ddUniqueCompare (void const *ptrX, void const *ptrY);
static int chooseSD3inPlace_bnet (DdManager * table,int level,BnetNetwork * network);
static int chooseSD6inPlace_bnet (DdManager * table,int level,BnetNetwork * network);
static int ddReorderPreprocess (DdManager *table);
static int ddReorderPostprocess (DdManager *table);
/** \endcond */


/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/


/**
  @brief Main dynamic reordering routine.

  @details Calls one of the possible reordering procedures:
  <ul>
  <li>Swapping
  <li>Sifting
  <li>Symmetric Sifting
  <li>Group Sifting
  <li>Window Permutation
  <li>Simulated Annealing
  <li>Genetic Algorithm
  <li>Dynamic Programming (exact)
  </ul>
  For sifting, symmetric sifting, group sifting, and window
  permutation it is possible to request reordering to convergence.<p>
  The core of all methods is the reordering procedure
  cuddSwapInPlace() which swaps two adjacent variables and is based
  on Rudell's paper.

  @return 1 in case of success; 0 otherwise. In the case of symmetric
  sifting (with and without convergence) returns 1 plus the number of
  symmetric variables, in case of success.

  @sideeffect Changes the variable order for all diagrams and clears
  the cache.

*/
int
bkfdd_reorder_bnet(
  DdManager * table /**< %DD manager */,
  Cudd_ReorderingType heuristic /**< method used for reordering */,
  int  minsize /**< bound below which no reordering occurs */,
  BnetNetwork *net)
{
	DdHook *hook;
	int	result;
	unsigned int nextDyn;
	#ifdef DD_STATS
	unsigned int initialSize;
	unsigned int finalSize;
	#endif
	unsigned long localTime;

	/* Don't reorder if there are too many dead nodes. */
	if (table->keys - table->dead < (unsigned) minsize)
	return(1);

	if (heuristic == CUDD_REORDER_SAME) {
	heuristic = table->autoMethod;
	}
	if (heuristic == CUDD_REORDER_NONE) {
	return(1);
	}

	/* This call to Cudd_ReduceHeap does initiate reordering. Therefore
	** we count it.
	*/
	table->reorderings++;

	localTime = util_cpu_time();

	/* Run the hook functions. */
	hook = table->preReorderingHook;
	while (hook != NULL) {
	int res = (hook->f)(table, "BDD", (void *)heuristic);
	if (res == 0) return(0);
	hook = hook->next;
	}

	if (!ddReorderPreprocess(table)) return(0);
	table->ddTotalNumberSwapping = 0;

	if (table->keys > table->peakLiveNodes) {
	table->peakLiveNodes = table->keys;
	}
	#ifdef DD_STATS
	initialSize = (int) (table->keys - table->isolated);
	table->totalNISwaps = 0;

	(void) fprintf(table->out,"%8d: initial size",initialSize);
	#endif

	/* See if we should use alternate threshold for maximum growth. */
	if (table->reordCycle && table->reorderings % table->reordCycle == 0) {
	double saveGrowth = table->maxGrowth;
	table->maxGrowth = table->maxGrowthAlt;
	result = odtSifting_bnet(table,0,table->size-1,net);
	table->maxGrowth = saveGrowth;
	} else {
	result = odtSifting_bnet(table,0,table->size-1,net);
	}

	#ifdef DD_STATS
	(void) fprintf(table->out,"\n");
	finalSize = (int) (table->keys - table->isolated);
	(void) fprintf(table->out,"#:F_REORDER %8d: final size\n",finalSize);
	(void) fprintf(table->out,"#:T_REORDER %8g: total time (sec)\n",
	((double)(util_cpu_time() - localTime)/1000.0));
	(void) fprintf(table->out,"#:N_REORDER %8d: total swaps\n",
	table->ddTotalNumberSwapping);
	(void) fprintf(table->out,"#:M_REORDER %8d: NI swaps\n",
	table->totalNISwaps);
	#endif

	if (result == 0)
	return(0);

	if (!ddReorderPostprocess(table))
	return(0);

	nextDyn = (table->keys - table->constants.keys + 1) *
	DD_DYN_RATIO + table->constants.keys;
	if (table->reorderings < 20 || nextDyn > table->nextDyn)
	table->nextDyn = nextDyn;
	else
	table->nextDyn += 20;
	if (table->randomizeOrder != 0) {
	table->nextDyn += Cudd_Random(table) & table->randomizeOrder;
	}
	table->reordered = 1;

	/* Run hook functions. */
	hook = table->postReorderingHook;
	while (hook != NULL) {
	int res = (hook->f)(table, "BDD", (void *)(ptruint)localTime);
	if (res == 0) return(0);
	hook = hook->next;
	}
	/* Update cumulative reordering time. */
	table->reordTime += util_cpu_time() - localTime;

	return(result);

} /* end of bkfdd_reorder_bnet */


/**
  @brief Implementation of BKFDD's odt-sifting algorithm. ORIGINAL VERSION of odt

  @details Assumes that no dead nodes are present.
    <ol>
    <li> Order all the variables according to the number of entries
    in each unique table.
    <li> Sift the variable up and down, if reach bottom level, 
	 change to different expansion types, remembering each time the
    total size of the %DD heap.
    <li> Select the best permutation.
    <li> Repeat 3 and 4 for all variables.
    </ol>

  @return 1 if successful; 0 otherwise.

  @sideeffect None

	@NOTE: No interact matrix, isolated projection counter,
	and lower bound estimation.	Since expansions are changed
	during sifting, these optimization techniques may become
	invalid the process.

*/
int
odtSifting_bnet(
	DdManager * table,
	int lower,
	int upper,
	BnetNetwork * network)
{
	int	i;
	IndexKey *var;
	int	size;
	int	x;
	int	result;
#ifdef DD_STATS
	int	previousSize;
#endif

	size = table->size;

	/* Find order in which to sift variables. */
	var = ALLOC(IndexKey,size);
	if (var == NULL) {
		table->errorCode = CUDD_MEMORY_OUT;
		goto odtSiftingFailed;
	}

	for (i = 0; i < size; i++) {
		x = table->perm[i];
		var[i].index = i;
		var[i].keys = table->subtables[x].keys;	// keys == number of nodes
	}

	util_qsort(var,size,sizeof(IndexKey),ddUniqueCompare);

	/* Now sift. */
	for (i = 0; i < ddMin(table->siftMaxVar,size); i++) {
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
		x = table->perm[var[i].index];

		if (x < lower || x > upper || table->subtables[x].bindVar == 1)
			continue;
#ifdef DD_STATS
		previousSize = (int) (table->keys - table->isolated);
#endif
		result = odtSiftingAux_bnet(table, x, lower, upper, network);
		if (!result) goto odtSiftingFailed;
#ifdef DD_STATS
		if (table->keys < (unsigned) previousSize + table->isolated) {
			(void) fprintf(table->out,"-");
		} else if (table->keys > (unsigned) previousSize + table->isolated) {
			(void) fprintf(table->out,"+");	/* should never happen */
			(void) fprintf(table->err,"\nSize increased from %d to %u while sifting variable %d\n", previousSize, table->keys - table->isolated, var[i].index);
		} else {
			(void) fprintf(table->out,"=");
		}
		fflush(table->out);
#endif
	}

	FREE(var);

	int CScount,BScount,CNDcount,BNDcount,CPDcount,BPDcount;
	BScount = CNDcount = BNDcount = CPDcount = BPDcount = 0;
	/* expansion type of bottom variable has no effect on DD size,
		so we assume the bottom variable associate with CS. */
	CScount = 1;
	for (i = 0; i < table->size-1; i ++) {
		switch(table->expansion[i]) {
			case CS:
				CScount ++;
				break;
			case CPD:
				CPDcount ++;
				break;
			case CND:
				CNDcount ++;
				break;
			case BS:
				BScount ++;
				break;
			case BPD:
				BPDcount ++;
				break;
			case BND:
				BNDcount ++;
				break;
			default:
				printf("unknown\n");
				break;
		}
	}

	int sum = CScount+BScount+CNDcount+BNDcount+CPDcount+BPDcount;
	assert(sum == table->size);
	printf("{ ");
	if (BNDcount || BPDcount || (BScount && (CNDcount || CPDcount))) {
		if (BNDcount || BPDcount) {
			printf("[BKFDD_1] ");
		} else {
			printf("[BKFDD_2] ");
		}
	} else if (BScount){
		printf("[BiDD] ");
	} else if (CNDcount || CPDcount) {
		printf("[KFDD] ");
	} else {
		printf("[BDD] ");
	}
	printf("CS:%d, BS:%d, CND:%d, BND:%d, CPD:%d, BPD:%d } ",
	CScount,BScount,CNDcount,BNDcount,CPDcount,BPDcount);

	return(1);

odtSiftingFailed:

	if (var != NULL) FREE(var);

	return(0);

} /* end of odtSifting_bnet */

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/

/**
  @brief In BKFDD's odt-sifting, Given xLow <= x <= xHigh moves x 
  up and down between the boundaries.
  If reach the bottom level, change expansion types.

  @details Finds the best position and does the required changes.

  @return 1 if successful; 0 otherwise.

  @sideeffect None

*/
static int
odtSiftingAux_bnet(
  DdManager * table,
  int  x,
  int  xLow,
  int  xHigh,
  BnetNetwork * network)
{

	Move	*move;
	Move	*moveUp;		/* list of up moves */
	Move	*moveDown;		/* list of down moves */
	Move	*bestPos;		/* Best position and expansion types */
	int		result;

	int xindex = table->invperm[x];

	moveDown = NULL;
	moveUp = NULL;

	bestPos = (Move *) cuddDynamicAllocNode(table);
	if (bestPos == NULL) goto odtSiftingAuxOutOfMem;
	/* Store initial information */
	bestPos->x = bestPos->y = x;
	bestPos->flags = table->expansion[x];
	bestPos->size = (int) (table->keys - table->isolated);;
	bestPos->next = NULL;

	if (x == xLow) {
		moveDown = odtSiftingDown_bnet(table,x,xHigh,bestPos,network);
		/* At this point x --> xHigh unless bounding occurred. */
		if (moveDown == (Move *) CUDD_OUT_OF_MEM) goto odtSiftingAuxOutOfMem;
		/* Move backward(up) and stop at best position. */
		result = odtSiftingBackward_bnet(table,table->perm[xindex],bestPos,network);
		if (!result) goto odtSiftingAuxOutOfMem;
	} else if (x == xHigh) {
		moveUp = odtSiftingUp_bnet(table,x,xLow,bestPos,network);
		/* At this point x --> xLow unless bounding occurred. */
		if (moveUp == (Move *) CUDD_OUT_OF_MEM) goto odtSiftingAuxOutOfMem;
		/* Move backward(down) and stop at best position. */
		result = odtSiftingBackward_bnet(table,table->perm[xindex],bestPos,network);
		if (!result) goto odtSiftingAuxOutOfMem;
	} else if ((x - xLow) > (xHigh - x)) { /* must go down first: shorter */
		moveDown = odtSiftingDown_bnet(table,x,xHigh,bestPos,network);
		/* At this point x --> xHigh unless bounding occurred. */
		if (moveDown == (Move *) CUDD_OUT_OF_MEM) goto odtSiftingAuxOutOfMem;
		if (moveDown != NULL) {
			x = moveDown->y;
		}
		moveUp = odtSiftingUp_bnet(table,x,xLow,bestPos,network);
		if (moveUp == (Move *) CUDD_OUT_OF_MEM) goto odtSiftingAuxOutOfMem;
		/* Move backward(down) and stop at best position */
		result = odtSiftingBackward_bnet(table,table->perm[xindex],bestPos,network);
		if (!result) goto odtSiftingAuxOutOfMem;
	} else {
		moveUp = odtSiftingUp_bnet(table,x,xLow,bestPos,network);
		/* At this point x --> xLow unless bounding occurred. */
		if (moveUp == (Move *) CUDD_OUT_OF_MEM) goto odtSiftingAuxOutOfMem;
		if (moveUp != NULL) {
			x = moveUp->x;
		}
		moveDown = odtSiftingDown_bnet(table,x,xHigh,bestPos,network);
		if (moveDown == (Move *) CUDD_OUT_OF_MEM) goto odtSiftingAuxOutOfMem;
		/* Move backward(up) and stop at best position. */
		result = odtSiftingBackward_bnet(table,table->perm[xindex],bestPos,network);
		if (!result) goto odtSiftingAuxOutOfMem;
	}
	
	if (isBi(table->expansion[table->size-1])) {
		if (!changeExpnBetweenBiCla_bnet(table, table->size-1,network)) {
			printf("odtSiftingAux: bottom Cla-expn failed\n");
			goto odtSiftingAuxOutOfMem;
		}
	}

	while (moveDown != NULL) {
		move = moveDown->next;
		cuddDeallocMove(table, moveDown);
		moveDown = move;
	}
	while (moveUp != NULL) {
		move = moveUp->next;
		cuddDeallocMove(table, moveUp);
		moveUp = move;
	}
	cuddDeallocMove(table, bestPos);
	
	return(1);

odtSiftingAuxOutOfMem:
	if (moveDown != (Move *) CUDD_OUT_OF_MEM) {
		while (moveDown != NULL) {
			move = moveDown->next;
			cuddDeallocMove(table, moveDown);
			moveDown = move;
		}
	}
	if (moveUp != (Move *) CUDD_OUT_OF_MEM) {
		while (moveUp != NULL) {
			move = moveUp->next;
			cuddDeallocMove(table, moveUp);
			moveUp = move;
		}
	}
	cuddDeallocMove(table, bestPos);

	return(0);

} /* end of odtSiftingAux_bnet */


/**
  @brief Sifts a variable up.

  @details Moves y up until either it reaches the bound (xLow) or the
  size of the %DD heap increases too much. BKFDD's odt-sifting 
  is similar to Rudell's sifting.

  @return the set of moves in case of success; NULL if memory is full.

  @sideeffect None

*/
static Move *
odtSiftingUp_bnet(
  	DdManager * table,
  	int y,
	int xLow,
	Move *best,
	BnetNetwork * network)
{
	Move	*moves;
	Move	*move;
	int	x;
	int	size;
	int	limitSize;

	moves = NULL;
	limitSize = (int) (table->keys - table->isolated);

	x = cuddNextLow(table,y);
	while (x >= xLow) {
		size = complexSwap_bnet(table,x,y,network);
		if (size == 0) goto odtSiftingUpOutOfMem;
		// change expansion
		if (!chooseSD6inPlace_bnet(table,x,network)) {
			goto odtSiftingUpOutOfMem;
		}
		size = (int) (table->keys - table->isolated);
		move = (Move *) cuddDynamicAllocNode(table);
		if (move == NULL) goto odtSiftingUpOutOfMem;
		if (size < best->size) { // store best position and expn
			best->x = best->y = x;
			best->size = size;
			best->flags = table->expansion[x];
		}
		move->x = x;
		move->y = y;
		move->size = size;
		move->next = moves;
		moves = move;
		if ((double) size > (double) limitSize * table->maxGrowth) break;
		if (size < limitSize) limitSize = size;
		y = x;
		x = cuddNextLow(table,y);
	}

	return(moves);

odtSiftingUpOutOfMem:
	while (moves != NULL) {
		move = moves->next;
		cuddDeallocMove(table, moves);
		moves = move;
	}

	return((Move *) CUDD_OUT_OF_MEM);

} /* end of odtSiftingUp_bnet */


/**
  @brief Sifts a variable down.

  @details Moves x down until either it reaches the bound (xHigh) or
  the size of the %DD heap increases too much. In BKFDD's odt-sifting,
  if reach the bottom level, change expansion types.

  @return the set of moves in case of success; NULL if memory is full.

  @sideeffect None

*/
static Move *
odtSiftingDown_bnet(
  DdManager * table,
  int x,
  int xHigh,
	Move *best,
	BnetNetwork * network)
{
	Move	*moves;
	Move	*move;
	int	y;
	int	size;
	int	limitSize;

	moves = NULL;
	limitSize = (int) (table->keys - table->isolated);

	y = cuddNextHigh(table,x);
	while (y <= xHigh) {
		size = complexSwap_bnet(table,x,y,network);
		if (size == 0) goto odtSiftingDownOutOfMem;
		// change expansion
		if (!chooseSD6inPlace_bnet(table,y,network)) {
			goto odtSiftingDownOutOfMem;
		}
		size = (int) (table->keys - table->isolated);
		move = (Move *) cuddDynamicAllocNode(table);
		if (move == NULL) goto odtSiftingDownOutOfMem;
		if (size < best->size) { // store best position and expn
			best->x = best->y = y;
			best->size = size;
			best->flags = table->expansion[y];
		}
		move->x = x;
		move->y = y;
		move->size = size;
		move->next = moves;
		moves = move;
		if ((double) size > (double) limitSize * table->maxGrowth) break;
		if (size < limitSize) limitSize = size;
		x = y;
		y = cuddNextHigh(table,x);
	}

	return(moves);

odtSiftingDownOutOfMem:
	while (moves != NULL) {
		move = moves->next;
		cuddDeallocMove(table, moves);
		moves = move;
	}

	return((Move *) CUDD_OUT_OF_MEM);

} /* end of odtSiftingDown_bnet */


/**
  @brief Given a set of moves, returns the %DD heap to the position
  giving the minimum size.

  @details In case of ties, returns to the closest position giving the
  minimum size.

  @return 1 in case of success; 0 otherwise.

  @sideeffect None

*/
static int
odtSiftingBackward_bnet(
	DdManager * table,
	int  currentPos,
	Move * best,
	BnetNetwork * network)
{
	int res, pos, expn;
	pos = best->x;
	expn = (int)best->flags;

	while (currentPos < pos) { // move down to best position
		res = complexSwap_bnet(table,currentPos,currentPos+1,network);
		if (res == 0) {
			printf("odtSiftingBackward: down to best failed\n");
			return(0);
		}
		currentPos ++;
	}
	while (currentPos > pos) { // move up to best position
		res = complexSwap_bnet(table,currentPos-1,currentPos,network);
		if (res == 0) {
			printf("odtSiftingBackward: up to best failed\n");
			return(0);
		}
		currentPos --;
	}
	assert(currentPos == pos);
	// change to best expn
	if (table->expansion[pos] != expn) {
		if ( (isBi(table->expansion[pos]) && isCla(expn)) ||
					(isCla(table->expansion[pos]) && isBi(expn)) ) {
			if (!changeExpnBetweenBiCla_bnet(table, pos,network)) {
				printf("odtSiftingBackward: roll back failed\n");
				return(0);
			}
		}
		if (table->expansion[pos] != expn) {
			if (isShan(table->expansion[pos])) {
					// S => ND
				if (isNDavio(expn)) {
					if (!changeExpnBetweenSND_bnet(table, pos,network)) {
						printf("odtSiftingBackward: roll back failed\n");
						return(0);
					}
				} else if (isPDavio(expn)) {
					// S => PD
					if (!changeExpnStoPD_bnet(table, pos,network)) {
						printf("odtSiftingBackward: roll back failed\n");
						return(0);
					}
				}
			} else if (isNDavio(table->expansion[pos])) {
				if (isShan(expn)) {
					// ND => S
					if (!changeExpnBetweenSND_bnet(table, pos,network)) {
						printf("odtSiftingBackward: roll back failed\n");
						return(0);
					}
				} else if (isPDavio(expn)) {
					// ND => PD
					if (!changeExpnBetweenNDPD_bnet(table, pos,network)) {
						printf("odtSiftingBackward: roll back failed\n");
						return(0);
					}
				}
			} else {
					// PD => S
				if (isShan(expn)) {
					if (!changeExpnPDtoS_bnet(table, pos,network)) {
						printf("odtSiftingBackward: roll back failed\n");
						return(0);
					}
				} else if (isNDavio(expn)) {
					// PD => ND
					if (!changeExpnBetweenNDPD_bnet(table, pos,network)) {
						printf("odtSiftingBackward: roll back failed\n");
						return(0);
					}
				}
			}
		}
	}
	assert(table->expansion[pos] == expn);
	assert((int)(table->keys-table->isolated) == best->size);

	return(1);

} /* end of odtSiftingBackward_bnet */


/**
  @brief Swaps two adjacent variables.
	 	1. Make sure two adjacent variables associated with cla-expn.
		2. Naive Swap two adjacent.
		3. Recover two adjacent to original expansions.
*/
static int
complexSwap_bnet(
  DdManager * table,
  int  x,
  int  y,
  BnetNetwork * network)
{

	DdNode *p = NULL;
	int yBi, xBi, x_1Bi, size, i;
	yBi = xBi = x_1Bi = size = 0;

	if (x > 0) {
		garbageCollectSimple(table,x-1);
	} else {
		garbageCollectSimple(table,x);
	}

	/* check counter of isolated projection. */
	unsigned int isolated = 0;
	for (i = 0; i < table->size; i ++) {
		p = Cudd_Regular(table->vars[i]);
		if (p->ref == 1) {
			isolated ++;
		}
	}
	assert(table->isolated == isolated);

	/* Make sure x-1, x, y are associated with cla-expn. */
	if (isBi(table->expansion[y])) {
		yBi = 1;
		if (!changeExpnBetweenBiCla_bnet(table, y,network)) {
			printf("complexSwap: change expn failed\n");
			goto swapFailed;
		}
	}

	if (isBi(table->expansion[x])) {
		xBi = 1;
		if (!changeExpnBetweenBiCla_bnet(table, x,network)) {
			printf("complexSwap: change expn failed\n");
			goto swapFailed;
		}
	}

	if ( (x > 0) && isBi(table->expansion[x-1])) {
		x_1Bi = 1;
		if (!changeExpnBetweenBiCla_bnet(table, x-1,network)) {
			printf("complexSwap: change expn failed\n");
			goto swapFailed;
		}
	}

	/* Swap x and y. */
	size = NaiveSwap(table, x, y);
	if (size == 0) {
		printf("complexSwap: swap failed\n");
		goto swapFailed;
	}

	/* Recover expansion types. */
	if (x_1Bi) {
		if (!changeExpnBetweenBiCla_bnet(table, x-1,network)) {
			printf("complexSwap: change expn failed\n");
			goto swapFailed;
		}
	}
	if (yBi) {
		if (!changeExpnBetweenBiCla_bnet(table, x,network)) {
			printf("complexSwap: change expn failed\n");
			goto swapFailed;
		}
	}
	if (xBi) {
		if (!changeExpnBetweenBiCla_bnet(table, y,network)) {
			printf("complexSwap: change expn failed\n");
			goto swapFailed;
		}
	}

	isolated = 0;
	for (i = 0; i < table->size; i ++) {
		p = Cudd_Regular(table->vars[i]);
		if (p->ref == 1) {
			isolated ++;
		}
	}
	assert(table->isolated == isolated);

	return (table->keys - table->isolated);

swapFailed:
	return(0);
} /* end of complexSwap_bnet */


/**
  @brief Comparison function used by qsort.

  @details Used to order the variables according to the number of keys
  in the subtables.

  @return the difference in number of keys between the two variables
  being compared.

  @sideeffect None

*/
static int
ddUniqueCompare(
  void const * ptrX,
  void const * ptrY)
{
  IndexKey const * pX = (IndexKey const *) ptrX;
  IndexKey const * pY = (IndexKey const *) ptrY;
  return(pY->keys - pX->keys);

} /* end of ddUniqueCompare */


/** 
	@brief choose better expansion from {CS, CND, CPD}
*/
static int
chooseSD3inPlace_bnet(
	DdManager * table,
	int level,
	BnetNetwork * network)
{
	unsigned int oldKeysTotal, newKeysTotal;
	unsigned int newKeysTotal1, newKeysTotal2;
	int ii, initExpn, expn1, expn2, expn;

	cuddCacheFlush(table);
	garbageCollectSimple(table,level);

	/* Re-count isolated variables. */
	unsigned int isolated = 0;
	for (ii = 0; ii < table->size; ii ++) {
		DdNode *p = Cudd_Regular(table->vars[ii]);
		if (p->ref == 1) {
			isolated ++;
		}
	}
	assert(table->isolated == isolated);

	oldKeysTotal = table->keys-table->isolated;
	/* some arguments */
	// number of davio expansions allowed to exist
	int davio_exist_bound = (int)(table->size * table->davio_exist_factor);
	// upper bound of number of davio expansions allowed to exist
	int upper_bound = 0;
	if (DAVIO_EXIST_BOUND > davio_exist_bound) {
		upper_bound = davio_exist_bound;
	} else {
		upper_bound = DAVIO_EXIST_BOUND;
	}
	// how many davio expansion exist currently
	int nonShan = 0;
	for (ii = 0; ii <= table->size-1; ii ++) {
		if (!isShan(table->expansion[ii])) {
			nonShan ++;
		}
	}

	if (table->subtables[level].keys == 0) { return(1); }
	if ( (nonShan == upper_bound) &&
			isShan(table->expansion[level]) ) {
		return(1);
	} else {
		/*
			1. nonShan == upper_bound and !isShan
			2. nonShan < upper_bound	and isShan
			3. nonShan < upper_bound  and !isShan
		*/
		initExpn = table->expansion[level];

		if (isShan(table->expansion[level])) {
			// CS->CND->CPD or BS->BND->BPD
			if (!changeExpnBetweenSND_bnet(table,level,network)) {
				printf("chooseSD3inPlace_bnet: %d, choose better expn failed\n", level);
				goto chooseFailed;
			}
			newKeysTotal1 = table->keys-table->isolated;
			expn1 = table->expansion[level];
			if (!changeExpnBetweenNDPD_bnet(table,level,network)) {
				printf("chooseSD3inPlace_bnet: %d, choose better expn failed\n", level);
				goto chooseFailed;
			}
			newKeysTotal2 = table->keys-table->isolated;
			expn2 = table->expansion[level];
			newKeysTotal = ddMin(newKeysTotal1, newKeysTotal2);
			if (newKeysTotal == newKeysTotal1) {
				expn = expn1;
			} else {
				expn = expn2;
			}

			int key = newKeysTotal;
			int keyNew = ceil(oldKeysTotal * table->choose_new_bound_factor);
			int keyDav = ceil(oldKeysTotal * table->choose_dav_bound_factor);
			if ( (key >= keyNew) || (key >= keyDav) ) {
				if (!changeExpnPDtoS_bnet(table,level,network)) {
					printf("chooseSD3inPlace_bnet: %d, choose better expn failed\n", level);
					goto chooseFailed;
				}
				assert((table->keys-table->isolated) == oldKeysTotal);
			} else {
				oldKeysTotal = newKeysTotal;
				if (newKeysTotal == newKeysTotal1) {
					if (!changeExpnBetweenNDPD_bnet(table,level,network)) {
						printf("chooseSD3inPlace_bnet: %d, choose better expn failed\n", level);
						goto chooseFailed;
					}
					assert((table->keys-table->isolated) == newKeysTotal1);
				}
			}
		} else if (isNDavio(table->expansion[level])) {
			// CND->CPD->CS or BND->BPD->BS
			if (!changeExpnBetweenNDPD_bnet(table,level,network)) {
				printf("chooseSD3inPlace_bnet: %d, choose better expn failed\n", level);
				goto chooseFailed;
			}
			newKeysTotal1 = table->keys-table->isolated;
			expn1 = table->expansion[level];
			if (!changeExpnPDtoS_bnet(table,level,network)) {
				printf("chooseSD3inPlace_bnet: %d, choose better expn failed\n", level);
				goto chooseFailed;
			}
			newKeysTotal2 = table->keys-table->isolated;
			expn2 = table->expansion[level];
			newKeysTotal = ddMin(newKeysTotal1, newKeysTotal2);
			if (newKeysTotal == newKeysTotal1) {
				expn = expn1;
			} else {
				expn = expn2;
			}

			int key = newKeysTotal;
			int keyNew = ceil(oldKeysTotal * table->choose_new_bound_factor);
			int keyDav = ceil(oldKeysTotal * table->choose_dav_bound_factor);
			if ( (key >= keyNew) ||
					(!isShan(expn) && (key >= keyDav)) ) {
				if (!changeExpnBetweenSND_bnet(table,level,network)) {
					printf("chooseSD3inPlace_bnet: %d, choose better expn failed\n", level);
					goto chooseFailed;					
				}
				assert((table->keys-table->isolated) == oldKeysTotal);
			} else {
				oldKeysTotal = newKeysTotal;
				if (newKeysTotal == newKeysTotal1) {
					if (!changeExpnStoPD_bnet(table,level,network)) {
						printf("chooseSD3inPlace_bnet: %d, choose better expn failed\n", level);
						goto chooseFailed;					
					}
					assert((table->keys-table->isolated) == newKeysTotal1);
				}
			}
		} else { // positive Davio
			// CPD->CS->CND or BPD->BS->BND
			if (!changeExpnPDtoS_bnet(table,level,network)) {
				printf("chooseSD3inPlace_bnet: %d, choose better expn failed\n", level);
				goto chooseFailed;
			}
			newKeysTotal1 = table->keys-table->isolated;
			expn1 = table->expansion[level];
			if (!changeExpnBetweenSND_bnet(table,level,network)) {
				printf("chooseSD3inPlace_bnet: %d, choose better expn failed\n", level);
				goto chooseFailed;
			}
			newKeysTotal2 = table->keys-table->isolated;
			expn2 = table->expansion[level];
			newKeysTotal = ddMin(newKeysTotal1, newKeysTotal2);
			if (newKeysTotal == newKeysTotal1) {
				expn = expn1;
			} else {
				expn = expn2;
			}

			int key = newKeysTotal;
			int keyNew = ceil(oldKeysTotal * table->choose_new_bound_factor);
			int keyDav = ceil(oldKeysTotal * table->choose_dav_bound_factor);
			if ( (key >= keyNew) ||
					(!isShan(expn) && (key >= keyDav)) ) {
				if (!changeExpnBetweenNDPD_bnet(table,level,network)) {
					printf("chooseSD3inPlace_bnet: %d, choose better expn failed\n", level);
					goto chooseFailed;					
				}
				assert((table->keys-table->isolated) == oldKeysTotal);
			} else {
				oldKeysTotal = newKeysTotal;
				if (newKeysTotal == newKeysTotal1) {
					if (!changeExpnBetweenSND_bnet(table,level,network)) {
						printf("chooseSD3inPlace_bnet: %d, choose better expn failed\n", level);
						goto chooseFailed;					
					}
					assert((table->keys-table->isolated) == newKeysTotal1);
				}
			}
		}
		// re-count nonShan
		if (isShan(initExpn) && !isShan(table->expansion[level])) {
			nonShan ++;
		} else if (!isShan(initExpn) && isShan(table->expansion[level])){
			nonShan --;
		}
		assert(nonShan <= upper_bound);
	}

	return(1);

chooseFailed:

	fprintf(table->err, "chooseSD3inPlace_bnet failed\n");
	return(0);

} /* End of chooseSD3inPlace_bnet */


/** 
	@brief choose better expansion from {CS, CND, CPD, BS, BND, BPD}
*/
static int
chooseSD6inPlace_bnet(
	DdManager * table,
	int level,
	BnetNetwork * network)
{	
	unsigned int oldKeysTotal, newKeysTotal, initKeysTotal;
	unsigned int newKeysTotal1, newKeysTotal2, newKeysTotal3, newKeysTotal4, newKeysTotal5;
	int ii, initExpn, expn1, expn2, expn3, expn4, expn5, expn;
	
	cuddCacheFlush(table);
	garbageCollectSimple(table,level);
	
	/* Re-count isolated variables. */
	unsigned int isolated = 0;
	for (ii = 0; ii < table->size; ii ++) {
		DdNode *p = Cudd_Regular(table->vars[ii]);
		if (p->ref == 1) {
			isolated ++;
		}
	}
	assert(table->isolated == isolated);
	
	initKeysTotal = oldKeysTotal = table->keys-table->isolated;
	/* some arguments */
	// number of davio expansions allowed to exist
	int davio_exist_bound = (int)(table->size * table->davio_exist_factor);
	// upper bound of number of davio expansions allowed to exist
	int upper_bound = 0;
	if (DAVIO_EXIST_BOUND > davio_exist_bound) {
		upper_bound = davio_exist_bound;
	} else {
		upper_bound = DAVIO_EXIST_BOUND;
	}
	// how many davio expansion exist currently
	int nonShan = 0;
	for (ii = 0; ii <= table->size-1; ii ++) {
		if (!isShan(table->expansion[ii])) {
			nonShan ++;
		}
	}
	
	assert(nonShan <= upper_bound);
	if (table->subtables[level].keys == 0) { return(1); }
	if ( (nonShan == upper_bound) &&
			isShan(table->expansion[level]) ) {
		/* If number of nonShan expansion reach upper bound
		and current level associated with Shan, then try BS or CS. */
		if (!changeExpnBetweenBiCla_bnet(table,level,network)) {
			printf("chooseSD6inPlace_bnet: %d, choose better expn failed\n", level);
			goto failed;
		}
		newKeysTotal = table->keys-table->isolated;

		int key = newKeysTotal;
		int keyNew = ceil(oldKeysTotal * table->choose_new_bound_factor);
		if ( key >= keyNew ) {
			if (!changeExpnBetweenBiCla_bnet(table,level,network)) {
				printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
				goto failed;
			}
			newKeysTotal = table->keys-table->isolated;
			assert(newKeysTotal == oldKeysTotal);
		} else {
			oldKeysTotal = newKeysTotal;
		}
	} else {
		/*
			1. nonShan == upper_bound and !isShan
			2. nonShan < upper_bound	and isShan
			3. nonShan < upper_bound  and !isShan
		*/
		initExpn = table->expansion[level];
/* 
CS->CPD->CND->BND->BPD->BS->CS or CND->CPD->CS->BS->BPD->BND->CND or CPD->CND->CS->BS->BND->BPD->CPD
BS->BPD->BND->CND->CPD->CS->BS or BND->BPD->BS->CS->CPD->CND->BND or BPD->BND->BS->CS->CND->CPD->BPD
*/ 
		if (isShan(table->expansion[level])) {
			// CS->CPD or BS->BPD
			if (!changeExpnStoPD_bnet(table,level,network)) {
				printf("chooseSD6inPlace_bnet: %d, choose better expn failed\n", level);
				goto failed;
			}
			newKeysTotal1 = table->keys-table->isolated;
			expn1 = table->expansion[level];
			// CPD->CND or BPD->BND
			if (!changeExpnBetweenNDPD_bnet(table,level,network)) {
				printf("chooseSD6inPlace_bnet: %d, choose better expn failed\n", level);
				goto failed;
			}
			newKeysTotal2 = table->keys-table->isolated;
			expn2 = table->expansion[level];
			// CND->BND or BND->CND
			if (!changeExpnBetweenBiCla_bnet(table,level,network)) {
				printf("chooseSD6inPlace_bnet: %d, choose better expn failed\n", level);
				goto failed;
			}
			newKeysTotal3 = table->keys-table->isolated;
			expn3 = table->expansion[level];
			// BND->BPD or CND->CPD
			if (!changeExpnBetweenNDPD_bnet(table,level,network)) {
				printf("chooseSD6inPlace_bnet: %d, choose better expn failed\n", level);
				goto failed;
			}
			newKeysTotal4 = table->keys-table->isolated;
			expn4 = table->expansion[level];
			// BPD->BS or CPD->CS
			if (!changeExpnPDtoS_bnet(table,level,network)) {
				printf("chooseSD6inPlace_bnet: %d, choose better expn failed\n", level);
				goto failed;
			}
			assert(isShan(table->expansion[level]));
			newKeysTotal5 = table->keys-table->isolated;
			expn5 = table->expansion[level];
			newKeysTotal = ddMin(newKeysTotal1, newKeysTotal2);
			newKeysTotal = ddMin(newKeysTotal, newKeysTotal3);
			newKeysTotal = ddMin(newKeysTotal, newKeysTotal4);
			newKeysTotal = ddMin(newKeysTotal, newKeysTotal5);
			if (newKeysTotal == newKeysTotal1) {
				expn = expn1;
			} else if (newKeysTotal == newKeysTotal2) {
				expn = expn2;
			} else if (newKeysTotal == newKeysTotal3) {
				expn = expn3;
			} else if (newKeysTotal == newKeysTotal4) {
				expn = expn4;
			} else {
				expn = expn5;
			}

			int key = newKeysTotal;
			int keyNew = ceil(oldKeysTotal * table->choose_new_bound_factor);
			int keyDav = ceil(oldKeysTotal * table->choose_dav_bound_factor);
			if ( (key >= keyNew) ||
					(!isShan(expn) && (key >= keyDav)) ) {
				if (!changeExpnBetweenBiCla_bnet(table,level,network)) {
					printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
					goto failed;
				}
				assert((table->keys-table->isolated) == oldKeysTotal);
			} else {
				if (newKeysTotal == newKeysTotal1) {
					if (!changeExpnBetweenBiCla_bnet(table,level,network)) {
						printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
						goto failed;
					}
					assert((table->keys-table->isolated) == oldKeysTotal);
					if (!changeExpnStoPD_bnet(table,level,network)) {
						printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
						goto failed;
					}
					assert((table->keys-table->isolated) == newKeysTotal1);
				} else if (newKeysTotal == newKeysTotal2) {
					if (!changeExpnStoPD_bnet(table,level,network)) {
						printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
						goto failed;
					}
					assert((table->keys-table->isolated) == newKeysTotal4);
					if (!changeExpnBetweenNDPD_bnet(table,level,network)) {
						printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
						goto failed;
					}
					assert((table->keys-table->isolated) == newKeysTotal3);
					if (!changeExpnBetweenBiCla_bnet(table,level,network)) {
						printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
						goto failed;
					}
					assert((table->keys-table->isolated) == newKeysTotal2);
				} else if (newKeysTotal == newKeysTotal3) {
					if (!changeExpnStoPD_bnet(table,level,network)) {
						printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
						goto failed;
					}
					assert((table->keys-table->isolated) == newKeysTotal4);
					if (!changeExpnBetweenNDPD_bnet(table,level,network)) {
						printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
						goto failed;
					}
					assert((table->keys-table->isolated) == newKeysTotal3);
				} else if (newKeysTotal == newKeysTotal4) {
					if (!changeExpnStoPD_bnet(table,level,network)) {
						printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
						goto failed;
					}
					assert((table->keys-table->isolated) == newKeysTotal4);
				}
				oldKeysTotal = newKeysTotal;
			}
		} else if (isNDavio(table->expansion[level])) {
			// CND->CPD or BND->BPD
			if (!changeExpnBetweenNDPD_bnet(table,level,network)) {
				printf("chooseSD6inPlace_bnet: %d, choose better expn failed\n", level);
				goto failed;
			}
			newKeysTotal1 = table->keys-table->isolated;
			expn1 = table->expansion[level];
			// CPD->CS or BPD->BS
			if (!changeExpnPDtoS_bnet(table,level,network)) {
				printf("chooseSD6inPlace_bnet: %d, choose better expn failed\n", level);
				goto failed;
			}
			newKeysTotal2 = table->keys-table->isolated;
			expn2 = table->expansion[level];
			// CS->BS or BS->CS
			if (!changeExpnBetweenBiCla_bnet(table,level,network)) {
				printf("chooseSD6inPlace_bnet: %d, choose better expn failed\n", level);
				goto failed;
			}
			newKeysTotal3 = table->keys-table->isolated;
			expn3 = table->expansion[level];
			// BS->BPD or CS->CPD
			if (!changeExpnStoPD_bnet(table,level,network)) {
				printf("chooseSD6inPlace_bnet: %d, choose better expn failed\n", level);
				goto failed;
			}
			newKeysTotal4 = table->keys-table->isolated;
			expn4 = table->expansion[level];
			// BPD->BND or CPD->CND
			if (!changeExpnBetweenNDPD_bnet(table,level,network)) {
				printf("chooseSD6inPlace_bnet: %d, choose better expn failed\n", level);
				goto failed;
			}
			assert(isNDavio(table->expansion[level]));
			newKeysTotal5 = table->keys-table->isolated;
			expn5 = table->expansion[level];
			newKeysTotal = ddMin(newKeysTotal1, newKeysTotal2);
			newKeysTotal = ddMin(newKeysTotal, newKeysTotal3);
			newKeysTotal = ddMin(newKeysTotal, newKeysTotal4);
			newKeysTotal = ddMin(newKeysTotal, newKeysTotal5);
			if (newKeysTotal == newKeysTotal1) {
				expn = expn1;
			} else if (newKeysTotal == newKeysTotal2) {
				expn = expn2;
			} else if (newKeysTotal == newKeysTotal3) {
				expn = expn3;
			} else if (newKeysTotal == newKeysTotal4) {
				expn = expn4;
			} else {
				expn = expn5;
			}

			int key = newKeysTotal;
			int keyNew = ceil(oldKeysTotal * table->choose_new_bound_factor);
			int keyDav = ceil(oldKeysTotal * table->choose_dav_bound_factor);
			if ( (key >= keyNew) ||
					(!isShan(expn) && (key >= keyDav)) ) {
				if (!changeExpnBetweenBiCla_bnet(table,level,network)) {
					printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
					goto failed;
				}
				assert((table->keys-table->isolated) == oldKeysTotal);
			} else {
				if (newKeysTotal == newKeysTotal1) {
					if (!changeExpnBetweenBiCla_bnet(table,level,network)) {
						printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
						goto failed;
					}
					assert((table->keys-table->isolated) == oldKeysTotal);
					if (!changeExpnBetweenNDPD_bnet(table,level,network)) {
						printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
						goto failed;
					}
					assert((table->keys-table->isolated) == newKeysTotal1);
				} else if (newKeysTotal == newKeysTotal2) {
					if (!changeExpnBetweenNDPD_bnet(table,level,network)) {
						printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
						goto failed;
					}
					assert((table->keys-table->isolated) == newKeysTotal4);
					if (!changeExpnPDtoS_bnet(table,level,network)) {
						printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
						goto failed;
					}
					assert((table->keys-table->isolated) == newKeysTotal3);
					if (!changeExpnBetweenBiCla_bnet(table,level,network)) {
						printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
						goto failed;
					}
					assert((table->keys-table->isolated) == newKeysTotal2);
				} else if (newKeysTotal == newKeysTotal3) {
					if (!changeExpnBetweenNDPD_bnet(table,level,network)) {
						printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
						goto failed;
					}
					assert((table->keys-table->isolated) == newKeysTotal4);
					if (!changeExpnPDtoS_bnet(table,level,network)) {
						printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
						goto failed;
					}
					assert((table->keys-table->isolated) == newKeysTotal3);
				} else if (newKeysTotal == newKeysTotal4) {
					if (!changeExpnBetweenNDPD_bnet(table,level,network)) {
						printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
						goto failed;
					}
					assert((table->keys-table->isolated) == newKeysTotal4);
				}
				oldKeysTotal = newKeysTotal;
			}
		} else { // positive Davio
			// CPD->CND->CS->BS->BND->BPD->CPD or BPD->BND->BS->CS->CND->CPD->BPD
			// CPD->CND or BPD->BND
			if (!changeExpnBetweenNDPD_bnet(table,level,network)) {
				printf("chooseSD6inPlace_bnet: %d, choose better expn failed\n", level);
				goto failed;
			}
			newKeysTotal1 = table->keys-table->isolated;
			expn1 = table->expansion[level];
			// CND->CS or BND->BS
			if (!changeExpnBetweenSND_bnet(table,level,network)) {
				printf("chooseSD6inPlace_bnet: %d, choose better expn failed\n", level);
				goto failed;
			}
			newKeysTotal2 = table->keys-table->isolated;
			expn2 = table->expansion[level];
			// CS->BS or BS->CS
			if (!changeExpnBetweenBiCla_bnet(table,level,network)) {
				printf("chooseSD6inPlace_bnet: %d, choose better expn failed\n", level);
				goto failed;
			}
			newKeysTotal3 = table->keys-table->isolated;
			expn3 = table->expansion[level];
			// BS->BND or CS->CND
			if (!changeExpnBetweenSND_bnet(table,level,network)) {
				printf("chooseSD6inPlace_bnet: %d, choose better expn failed\n", level);
				goto failed;
			}
			newKeysTotal4 = table->keys-table->isolated;
			expn4 = table->expansion[level];
			// BND->BPD or CND->CPD
			if (!changeExpnBetweenNDPD_bnet(table,level,network)) {
				printf("chooseSD6inPlace_bnet: %d, choose better expn failed\n", level);
				goto failed;
			}
			assert(isPDavio(table->expansion[level]));
			newKeysTotal5 = table->keys-table->isolated;
			expn5 = table->expansion[level];
			newKeysTotal = ddMin(newKeysTotal1, newKeysTotal2);
			newKeysTotal = ddMin(newKeysTotal, newKeysTotal3);
			newKeysTotal = ddMin(newKeysTotal, newKeysTotal4);
			newKeysTotal = ddMin(newKeysTotal, newKeysTotal5);
			if (newKeysTotal == newKeysTotal1) {
				expn = expn1;
			} else if (newKeysTotal == newKeysTotal2) {
				expn = expn2;
			} else if (newKeysTotal == newKeysTotal3) {
				expn = expn3;
			} else if (newKeysTotal == newKeysTotal4) {
				expn = expn4;
			} else {
				expn = expn5;
			}

			int key = newKeysTotal;
			int keyNew = ceil(oldKeysTotal * table->choose_new_bound_factor);
			int keyDav = ceil(oldKeysTotal * table->choose_dav_bound_factor);
			if ( (key >= keyNew) ||
					(!isShan(expn) && (key >= keyDav)) ) {
				if (!changeExpnBetweenBiCla_bnet(table,level,network)) {
					printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
					goto failed;
				}
				assert((table->keys-table->isolated) == oldKeysTotal);
			} else {
				if (newKeysTotal == newKeysTotal1) {
					if (!changeExpnBetweenBiCla_bnet(table,level,network)) {
						printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
						goto failed;
					}
					assert((table->keys-table->isolated) == oldKeysTotal);
					if (!changeExpnBetweenNDPD_bnet(table,level,network)) {
						printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
						goto failed;
					}
					assert((table->keys-table->isolated) == newKeysTotal1);
				} else if (newKeysTotal == newKeysTotal2) {
					if (!changeExpnBetweenNDPD_bnet(table,level,network)) {
						printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
						goto failed;
					}
					assert((table->keys-table->isolated) == newKeysTotal4);
					if (!changeExpnBetweenSND_bnet(table,level,network)) {
						printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
						goto failed;
					}
					assert((table->keys-table->isolated) == newKeysTotal3);
					if (!changeExpnBetweenBiCla_bnet(table,level,network)) {
						printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
						goto failed;
					}
					assert((table->keys-table->isolated) == newKeysTotal2);
				} else if (newKeysTotal == newKeysTotal3) {
					if (!changeExpnBetweenNDPD_bnet(table,level,network)) {
						printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
						goto failed;
					}
					assert((table->keys-table->isolated) == newKeysTotal4);
					if (!changeExpnBetweenSND_bnet(table,level,network)) {
						printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
						goto failed;
					}
					assert((table->keys-table->isolated) == newKeysTotal3);
				} else if (newKeysTotal == newKeysTotal4) {
					if (!changeExpnBetweenNDPD_bnet(table,level,network)) {
						printf("chooseSD6inPlace_bnet: %d, roll back failed\n", level);
						goto failed;
					}
					assert((table->keys-table->isolated) == newKeysTotal4);
				}
				oldKeysTotal = newKeysTotal;
			}
		}
		// re-count nonShan
		if (isShan(initExpn) && !isShan(table->expansion[level])) {
			nonShan ++;
		} else if (!isShan(initExpn) && isShan(table->expansion[level])){
			nonShan --;
		}
		assert(nonShan <= upper_bound);
	}

	return(1);

failed:

	fprintf(table->err, "chooseSD6_restricted failed\n");
	return(0);
} /* chooseSD6inPlace_bnet */


/**
  @brief Prepares the %DD heap for dynamic reordering.

  @details Does garbage collection, to guarantee that there are no
  dead nodes; clears the cache, which is invalidated by dynamic
  reordering; initializes the number of isolated projection functions;
  and initializes the interaction matrix.

  @return 1 in case of success; 0 otherwise.

  @sideeffect None

*/
static int
ddReorderPreprocess(
  DdManager * table)
{
	int i;
	int res;

	/* Clear the cache. */
	cuddCacheFlush(table);
	cuddLocalCacheClearAll(table);

	/* Eliminate dead nodes. Do not scan the cache again. */
	cuddGarbageCollect(table,0);

	/* Initialize number of isolated projection functions. */
	table->isolated = 0;
/** Xuanxiang Huang:BKFDD */
	for (i = 0; i < table->size; i++) {
		if (Cudd_Regular(table->vars[i])->ref == 1) table->isolated++;
	}
/** Xuanxiang Huang:BKFDD */

	/* Initialize the interaction matrix. */
	res = cuddInitInteract(table);
	if (res == 0) return(0);

	return(1);

} /* end of ddReorderPreprocess */


/**
  @brief Cleans up at the end of reordering.

  @sideeffect None

*/
static int
ddReorderPostprocess(
  DdManager * table)
{

#ifdef DD_VERBOSE
	(void) fflush(table->out);
#endif
	/* Free interaction matrix. */
	FREE(table->interact);

	return(1);

} /* end of ddReorderPostprocess */