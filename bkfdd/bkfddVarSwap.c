/**
  @file

  @ingroup bkfdd

  @brief Functions for swapping two adjacent BKFDD variables.

  @author Xuanxiang Huang

	@copyright
  Copyright (c) 2019-, Jinan University, Guangzhou, China.

  All rights reserved.

======================================================================
	All functions are originate from cuddReorder.c
	
	@Modification and Extension details
		1. Extend cuddSwapInPlace to adjacent non-Shannon decomposed nodes.
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
#include "bkfddInt.h"

static int Bkfdd_S_D_SwapInPlace (DdManager *table, int x, int y);
static int Bkfdd_D_S_SwapInPlace (DdManager *table, int x, int y);
static int Bkfdd_D_D_SwapInPlace (DdManager *table, int x, int y);

/* Swap two adjacent variables, a Naive version. */
static int naive_S_S_Swap (DdManager *table, int x, int y);
static int naive_S_D_Swap (DdManager *table, int x, int y);
static int naive_D_S_Swap (DdManager *table, int x, int y);
static int naive_D_D_Swap (DdManager *table, int x, int y);

/** 
	@brief Swaps two adjacent variables.
	
*/
int 
BkfddSwapInPlace(
	DdManager *table,
	int x,
	int y)
{
	int xdec = table->expansion[x];
	int ydec = table->expansion[y];
	int size;

	if (isShan(xdec)) {
		if (isShan(ydec)) {
			size = cuddSwapInPlace(table,x,y);
		} else {
			size = Bkfdd_S_D_SwapInPlace(table,x,y);
		}
	} else {
		if (isShan(ydec)) {
			size = Bkfdd_D_S_SwapInPlace(table,x,y);
		} else {
			size = Bkfdd_D_D_SwapInPlace(table,x,y);
		}
	}

	/* Exchange expansion types. */
	table->expansion[x] = ydec;
	table->expansion[y] = xdec;

	return(size);
} /* end of BkfddSwapInPlace */


/** 
	@brief Swaps two adjacent variables.
	@details a Naive version, without considering interact
	matrix, and other optimization techniques.
	
*/
int 
NaiveSwap(
	DdManager *table,
	int x,
	int y)
{
	int xdec = table->expansion[x];
	int ydec = table->expansion[y];
	assert(isCla(xdec) && isCla(ydec));
	int size;

	if (isShan(xdec)) {
		if (isShan(ydec)) {
			size = naive_S_S_Swap(table,x,y);
		} else {
			size = naive_S_D_Swap(table,x,y);
		}
	} else {
		if (isShan(ydec)) {
			size = naive_D_S_Swap(table,x,y);
		} else {
			size = naive_D_D_Swap(table,x,y);
		}
	}

	/* Exchange expansion types. */
	table->expansion[x] = ydec;
	table->expansion[y] = xdec;

	return(size);
} /* end of NaiveSwap */


/**
	@brief Swaps two S-D adjacent variables.

	@details It assumes that no dead nodes are present on entry to this
	procedure.  The procedure then guarantees that no dead nodes will be
	present when it terminates.  Bkfdd_S_D_SwapInPlace assumes that x &lt; y.
	It will alter the expansion-array, change S-D to D-S.

	Expansion types won't be checked inside the algorithm,
	make sure x with S, y with D before swapping.

	@return the number of keys in the table if successful; 0 otherwise.

	@sideeffect None

	In BDD, f1 means (var equiv. 1), f0 means (var equiv.0)
	In BBDD, f1 means f(index equiv. auxFunc), f0 means (index !equiv. auxFunc).

	In the following, use f1 to denote low-successor of f, f0 to denote
	high-successor of f.

*/
static int
Bkfdd_S_D_SwapInPlace(
	DdManager * table,
	int x,
	int y)
{
	DdNodePtr *xlist, *ylist;
	int xindex, yindex;
	int xslots, yslots;
	int xshift, yshift;
	int oldxkeys, oldykeys;
	int newxkeys, newykeys;
	int comple, newcomplement;
	int i;
	Cudd_VariableType varType;
	Cudd_LazyGroupType groupType;
	int posn;
	int isolated;
	DdNode *f,*f0,*f1,*f01,*f00,*f11,*f10,*newf1,*newf0;
	DdNode *g,*next;
	DdNodePtr *previousP;
	DdNode *tmp;
	DdNode *sentinel = &(table->sentinel);
	extern DD_OOMFP MMoutOfMemory;
	DD_OOMFP saveHandler;

#ifdef DD_DEBUG
	int    count,idcheck;
#endif

#ifdef DD_DEBUG
	assert(x < y);
	assert(cuddNextHigh(table,x) == y);
	assert(table->subtables[x].keys != 0);
	assert(table->subtables[y].keys != 0);
	assert(table->subtables[x].dead == 0);
	assert(table->subtables[y].dead == 0);
#endif

	table->ddTotalNumberSwapping++;

	/* Get parameters of x subtable. */
	xindex = table->invperm[x];
	xlist = table->subtables[x].nodelist;
	oldxkeys = table->subtables[x].keys;
	xslots = table->subtables[x].slots;
	xshift = table->subtables[x].shift;

	/* Get parameters of y subtable. */
	yindex = table->invperm[y];
	ylist = table->subtables[y].nodelist;
	oldykeys = table->subtables[y].keys;
	yslots = table->subtables[y].slots;
	yshift = table->subtables[y].shift;

	if (!cuddTestInteract(table,xindex,yindex)) {
#ifdef DD_STATS
		table->totalNISwaps++;
#endif
		newxkeys = oldxkeys;
		newykeys = oldykeys;
	} else {
		newxkeys = 0;
		newykeys = oldykeys;

		/* Check whether the two projection functions involved in this
		** swap are isolated. At the end, we'll be able to tell how many
		** isolated projection functions are there by checking only these
		** two functions again. This is done to eliminate the isolated
		** projection functions from the node count.
		*/
		isolated = - ((Cudd_Regular(table->vars[xindex])->ref == 1) +
		(Cudd_Regular(table->vars[yindex])->ref == 1));

		/* The nodes in the x layer that do not depend on
		** y will stay there; the others are put in a chain.
		** The chain is handled as a LIFO; g points to the beginning.
		*/
		g = NULL;
		if ((oldxkeys >= xslots || (unsigned) xslots == table->initSlots) &&
		oldxkeys <= DD_MAX_SUBTABLE_DENSITY * xslots) {
			for (i = 0; i < xslots; i++) {
				previousP = &(xlist[i]);
				f = *previousP;
				while (f != sentinel) {
					next = f->next;
					f1 = cuddT(f); f0 = cuddE(f);
					if (f1->index != (DdHalfWord) yindex &&
					Cudd_Regular(f0)->index != (DdHalfWord) yindex) {
						/* stays */	// the function doesn't depend on yindex.
						newxkeys++;
						*previousP = f;
						previousP = &(f->next);
					} else {
						f->index = yindex;
						f->next = g;
						g = f;
					}
					f = next;
				} /* while there are elements in the collision chain */
				*previousP = sentinel;
			} /* for each slot of the x subtable */
		} else {		/* resize xlist */
			DdNode *h = NULL;
			DdNodePtr *newxlist;
			unsigned int newxslots;
			int newxshift;
			/* Empty current xlist. Nodes that stay go to list h;
			** nodes that move go to list g. */
			for (i = 0; i < xslots; i++) {
				f = xlist[i];
				while (f != sentinel) {
					next = f->next;
					f1 = cuddT(f); f0 = cuddE(f);
					if (f1->index != (DdHalfWord) yindex &&
					Cudd_Regular(f0)->index != (DdHalfWord) yindex) {
						/* stays */
						f->next = h;
						h = f;
						newxkeys++;
					} else {
						f->index = yindex;
						f->next = g;
						g = f;
					}
					f = next;
				} /* while there are elements in the collision chain */
			} /* for each slot of the x subtable */
			/* Decide size of new subtable. */
			newxshift = xshift;
			newxslots = xslots;
			while ((unsigned) oldxkeys > DD_MAX_SUBTABLE_DENSITY * newxslots) {
				newxshift--;
				newxslots <<= 1;
			}
			while ((unsigned) oldxkeys < newxslots &&
			newxslots > table->initSlots) {
				newxshift++;
				newxslots >>= 1;
			}
			/* Try to allocate new table. Be ready to back off. */
			saveHandler = MMoutOfMemory;
			MMoutOfMemory = table->outOfMemCallback;
			newxlist = ALLOC(DdNodePtr, newxslots);
			MMoutOfMemory = saveHandler;
			if (newxlist == NULL) {
				(void) fprintf(table->err, "Unable to resize subtable %d for lack of memory\n", i);
			} else {
				table->slots += ((int) newxslots - xslots);
				table->minDead = (unsigned)
				(table->gcFrac * (double) table->slots);
				table->cacheSlack = (int)
				ddMin(table->maxCacheHard, DD_MAX_CACHE_TO_SLOTS_RATIO
				* table->slots) - 2 * (int) table->cacheSlots;
				table->memused +=
				((int) newxslots - xslots) * sizeof(DdNodePtr);
				FREE(xlist);
				xslots =  newxslots;
				xshift = newxshift;
				xlist = newxlist;
			}
			/* Initialize new subtable. */
			for (i = 0; i < xslots; i++) {
				xlist[i] = sentinel;
			}
			/* Move nodes that were parked in list h to their new home. */
			f = h;
			while (f != NULL) {
				next = f->next;
				f1 = cuddT(f);
				f0 = cuddE(f);
				/* Check xlist for pair (f11,f01). */
				posn = ddHash(f1, f0, xshift);
				/* For each element tmp in collision list xlist[posn]. */
				/* Nodes in collision list are arrange in the following manner,
					For node n1, n2:  
					If n1->T > n2->T 
								then n1 > n2;
					ELse if n1->T == n2->T
								then if n1->E > n2->E 
												then n1 > n2;
					NOTE 1. Sentinel is the least element, at the rear of xlist.
				*/
				previousP = &(xlist[posn]);
				tmp = *previousP;
				while (f1 < cuddT(tmp)) {
					previousP = &(tmp->next);
					tmp = *previousP;
				}
				while (f1 == cuddT(tmp) && f0 < cuddE(tmp)) {
					previousP = &(tmp->next);
					tmp = *previousP;
				}
				f->next = *previousP;
				*previousP = f;
				f = next;
			}
		}

#ifdef DD_COUNT
		table->swapSteps += oldxkeys - newxkeys;
#endif
		/* Take care of the x nodes that must be re-expressed.
		** They form a linked list pointed by g. Their index has been
		** already changed to yindex.
		*/
		f = g;
		while (f != NULL) {
			next = f->next;
			/* Find f1, f0, f11, f10, f01, f00. */
			f1 = cuddT(f);
#ifdef DD_DEBUG
			assert(!(Cudd_IsComplement(f1)));
#endif
			/* Before swap: f are decomposed by shannon expansion,
			** while f1, f0 are decomposed by davio expansions.
			** After swap: f are decomposed by davio expansions,
			** while newf1, newf0 are decomposed by shannon expansion.
			*/
			if ((int) f1->index == yindex) {
				f11 = cuddT(f1); f10 = cuddE(f1);
			} else {
				f11 = f1;
				f10 = Cudd_Not(DD_ONE(table));
			}
#ifdef DD_DEBUG
			assert(!(Cudd_IsComplement(f11)));
#endif
			f0 = cuddE(f);
			comple = Cudd_IsComplement(f0);
			f0 = Cudd_Regular(f0);
			if ((int) f0->index == yindex) {
				f01 = cuddT(f0); f00 = cuddE(f0);
			} else {
				f01 = f0;
				f00 = Cudd_Not(DD_ONE(table));
			}
			if (comple) {
				f01 = Cudd_Not(f01);
			}
			/* Decrease ref count of f1. */
			cuddSatDec(f1->ref);
			/* Create the new T child. */
			if (f11 == f01) {
				newf1 = f11;
				cuddSatInc(newf1->ref);
			} else {
				/* Check xlist for triple (xindex,f11,f01). */
				posn = ddHash(f11, f01, xshift);
				/* For each element newf1 in collision list xlist[posn]. */
				previousP = &(xlist[posn]);
				newf1 = *previousP;
				while (f11 < cuddT(newf1)) {
					previousP = &(newf1->next);
					newf1 = *previousP;
				}
				while (f11 == cuddT(newf1) && f01 < cuddE(newf1)) {
					previousP = &(newf1->next);
					newf1 = *previousP;
				}
				if (cuddT(newf1) == f11 && cuddE(newf1) == f01) {
					cuddSatInc(newf1->ref);
				} else { /* no match */
					newf1 = cuddDynamicAllocNode(table);
					if (newf1 == NULL) goto cuddSwapOutOfMem;
					newf1->index = xindex; newf1->ref = 1;
					cuddT(newf1) = f11;
					cuddE(newf1) = f01;
					/* Insert newf1 in the collision list xlist[posn];
					** increase the ref counts of f11 and f01.
					*/
					newxkeys++;
					newf1->next = *previousP;
					*previousP = newf1;
					cuddSatInc(f11->ref);
					tmp = Cudd_Regular(f01);
					cuddSatInc(tmp->ref);
				}
			}
			cuddT(f) = newf1;
#ifdef DD_DEBUG
			assert(!(Cudd_IsComplement(newf1)));
#endif

			/* Do the same for f0, keeping complement dots into account. */
			/* Decrease ref count of f0. */
			tmp = Cudd_Regular(f0);
			cuddSatDec(tmp->ref);
			/* Create the new E child. */
			if (f10 == f00) {
				newf0 = f00;
				tmp = Cudd_Regular(newf0);
				cuddSatInc(tmp->ref);
			} else {
				/* make sure f10 is regular */
				newcomplement = Cudd_IsComplement(f10);
				if (newcomplement) {
					f10 = Cudd_Not(f10);
					f00 = Cudd_Not(f00);
				}
				/* Check xlist for triple (xindex,f10,f00). */
				posn = ddHash(f10, f00, xshift);
				/* For each element newf0 in collision list xlist[posn]. */
				previousP = &(xlist[posn]);
				newf0 = *previousP;
				while (f10 < cuddT(newf0)) {
					previousP = &(newf0->next);
					newf0 = *previousP;
				}
				while (f10 == cuddT(newf0) && f00 < cuddE(newf0)) {
					previousP = &(newf0->next);
					newf0 = *previousP;
				}
				if (cuddT(newf0) == f10 && cuddE(newf0) == f00) {
					cuddSatInc(newf0->ref);
				} else { /* no match */
					newf0 = cuddDynamicAllocNode(table);
					if (newf0 == NULL) goto cuddSwapOutOfMem;
					newf0->index = xindex; newf0->ref = 1;
					cuddT(newf0) = f10;
					cuddE(newf0) = f00;
					/* Insert newf0 in the collision list xlist[posn];
					** increase the ref counts of f10 and f00.
					*/
					newxkeys++;
					newf0->next = *previousP;
					*previousP = newf0;
					cuddSatInc(f10->ref);
					tmp = Cudd_Regular(f00);
					cuddSatInc(tmp->ref);
				}
				if (newcomplement) {
					newf0 = Cudd_Not(newf0);
				}
			}
			cuddE(f) = newf0;

			/* Insert the modified f in ylist.
			** The modified f does not already exists in ylist.
			** (Because of the uniqueness of the cofactors.)
			*/
			posn = ddHash(newf1, newf0, yshift);
			newykeys++;
			previousP = &(ylist[posn]);
			tmp = *previousP;
			while (newf1 < cuddT(tmp)) {
				previousP = &(tmp->next);
				tmp = *previousP;
			}
			while (newf1 == cuddT(tmp) && newf0 < cuddE(tmp)) {
				previousP = &(tmp->next);
				tmp = *previousP;
			}
			f->next = *previousP;
			*previousP = f;
			f = next;
		} /* while f != NULL */

		/* GC the y layer. */

		/* For each node f in ylist. */
		for (i = 0; i < yslots; i++) {
			previousP = &(ylist[i]);
			f = *previousP;
			while (f != sentinel) {
				next = f->next;
				if (f->ref == 0) {
					tmp = cuddT(f);
					cuddSatDec(tmp->ref);
					tmp = Cudd_Regular(cuddE(f));
					cuddSatDec(tmp->ref);
					cuddDeallocNode(table,f);
					newykeys--;
				} else {
					*previousP = f;
					previousP = &(f->next);
				}
				f = next;
			} /* while f */
			*previousP = sentinel;
		} /* for i */

#ifdef DD_DEBUG
		count = 0;
		idcheck = 0;
		for (i = 0; i < yslots; i++) {
			f = ylist[i];
			while (f != sentinel) {
				count++;
				if (f->index != (DdHalfWord) yindex)
					idcheck++;
				f = f->next;
			}
		}
		if (count != newykeys) {
			(void) fprintf(table->out,
			"Error in finding newykeys\toldykeys = %d\tnewykeys = %d\tactual = %d\n",
			oldykeys,newykeys,count);
		}
		if (idcheck != 0)
			(void) fprintf(table->out,
			"Error in id's of ylist\twrong id's = %d\n",
			idcheck);
		count = 0;
		idcheck = 0;
		for (i = 0; i < xslots; i++) {
			f = xlist[i];
			while (f != sentinel) {
				count++;
				if (f->index != (DdHalfWord) xindex)
					idcheck++;
				f = f->next;
			}
		}
		if (count != newxkeys) {
			(void) fprintf(table->out,
			"Error in finding newxkeys\toldxkeys = %d \tnewxkeys = %d \tactual = %d\n",
			oldxkeys,newxkeys,count);
		}
		if (idcheck != 0)
			(void) fprintf(table->out,
			"Error in id's of xlist\twrong id's = %d\n",
			idcheck);
#endif

		isolated += (Cudd_Regular(table->vars[xindex])->ref == 1) +
	 (Cudd_Regular(table->vars[yindex])->ref == 1);
		table->isolated += (unsigned int) isolated;
	}

	/* Set the appropriate fields in table. */
	table->subtables[x].nodelist = ylist;
	table->subtables[x].slots = yslots;
	table->subtables[x].shift = yshift;
	table->subtables[x].keys = newykeys;
	table->subtables[x].maxKeys = yslots * DD_MAX_SUBTABLE_DENSITY;
	i = table->subtables[x].bindVar;
	table->subtables[x].bindVar = table->subtables[y].bindVar;
	table->subtables[y].bindVar = i;
	/* Adjust fields for lazy sifting. */
	varType = table->subtables[x].varType;
	table->subtables[x].varType = table->subtables[y].varType;
	table->subtables[y].varType = varType;
	i = table->subtables[x].pairIndex;
	table->subtables[x].pairIndex = table->subtables[y].pairIndex;
	table->subtables[y].pairIndex = i;
	i = table->subtables[x].varHandled;
	table->subtables[x].varHandled = table->subtables[y].varHandled;
	table->subtables[y].varHandled = i;
	groupType = table->subtables[x].varToBeGrouped;
	table->subtables[x].varToBeGrouped = table->subtables[y].varToBeGrouped;
	table->subtables[y].varToBeGrouped = groupType;

	table->subtables[y].nodelist = xlist;
	table->subtables[y].slots = xslots;
	table->subtables[y].shift = xshift;
	table->subtables[y].keys = newxkeys;
	table->subtables[y].maxKeys = xslots * DD_MAX_SUBTABLE_DENSITY;

	table->perm[xindex] = y; table->perm[yindex] = x;
	table->invperm[x] = yindex; table->invperm[y] = xindex;

	table->keys += newxkeys + newykeys - oldxkeys - oldykeys;

	return((int)(table->keys - table->isolated));

cuddSwapOutOfMem:
	(void) fprintf(table->err,"Error: Bkfdd_S_D_SwapInPlace out of memory\n");

	return (0);

} /* end of Bkfdd_S_D_SwapInPlace */


/**
	@brief Swaps two D-S adjacent variables.

	@details It assumes that no dead nodes are present on entry to this
	procedure.  The procedure then guarantees that no dead nodes will be
	present when it terminates.  Bkfdd_D_S_SwapInPlace assumes that x &lt; y.
	It will alter the expansion-array, change D-S to S-D.
	
	Expansion types won't be checked inside the algorithm,
	make sure x with D, y with S before swapping.

	@return the number of keys in the table if successful; 0 otherwise.

	@sideeffect None

	In the following, use f1 to denote low-successor of f, f0 to denote
	high-successor of f.

*/
static int
Bkfdd_D_S_SwapInPlace(
	DdManager * table,
	int x,
	int y)
{
	DdNodePtr *xlist, *ylist;
	int xindex, yindex;
	int xslots, yslots;
	int xshift, yshift;
	int oldxkeys, oldykeys;
	int newxkeys, newykeys;
	int comple, newcomplement;
	int i;
	Cudd_VariableType varType;
	Cudd_LazyGroupType groupType;
	int posn;
	int isolated;
	DdNode *f,*f0,*f1,*f01,*f00,*f11,*f10,*newf1,*newf0;
	DdNode *g,*next;
	DdNodePtr *previousP;
	DdNode *tmp;
	DdNode *sentinel = &(table->sentinel);
	extern DD_OOMFP MMoutOfMemory;
	DD_OOMFP saveHandler;

#ifdef DD_DEBUG
	int count,idcheck;
#endif

#ifdef DD_DEBUG
	assert(x < y);
	assert(cuddNextHigh(table,x) == y);
	assert(table->subtables[x].keys != 0);
	assert(table->subtables[y].keys != 0);
	assert(table->subtables[x].dead == 0);
	assert(table->subtables[y].dead == 0);
#endif

	table->ddTotalNumberSwapping++;

	/* Get parameters of x subtable. */
	xindex = table->invperm[x];
	xlist = table->subtables[x].nodelist;
	oldxkeys = table->subtables[x].keys;
	xslots = table->subtables[x].slots;
	xshift = table->subtables[x].shift;

	/* Get parameters of y subtable. */
	yindex = table->invperm[y];
	ylist = table->subtables[y].nodelist;
	oldykeys = table->subtables[y].keys;
	yslots = table->subtables[y].slots;
	yshift = table->subtables[y].shift;

	if (!cuddTestInteract(table,xindex,yindex)) {
#ifdef DD_STATS
		table->totalNISwaps++;
#endif
		newxkeys = oldxkeys;
		newykeys = oldykeys;
	} else {
		newxkeys = 0;
		newykeys = oldykeys;

		/* Check whether the two projection functions involved in this
		** swap are isolated. At the end, we'll be able to tell how many
		** isolated projection functions are there by checking only these
		** two functions again. This is done to eliminate the isolated
		** projection functions from the node count.
		*/
		isolated = - ((Cudd_Regular(table->vars[xindex])->ref == 1) +
		(Cudd_Regular(table->vars[yindex])->ref == 1));

		/* The nodes in the x layer that do not depend on
		** y will stay there; the others are put in a chain.
		** The chain is handled as a LIFO; g points to the beginning.
		*/
		g = NULL;
		if ((oldxkeys >= xslots || (unsigned) xslots == table->initSlots) &&
		oldxkeys <= DD_MAX_SUBTABLE_DENSITY * xslots) {
			for (i = 0; i < xslots; i++) {
				previousP = &(xlist[i]);
				f = *previousP;
				while (f != sentinel) {
					next = f->next;
					f1 = cuddT(f); f0 = cuddE(f);
					if (f1->index != (DdHalfWord) yindex &&
					Cudd_Regular(f0)->index != (DdHalfWord) yindex) {
						/* stays */
						newxkeys++;
						*previousP = f;
						previousP = &(f->next);
					} else {
						f->index = yindex;
						f->next = g;
						g = f;
					}
					f = next;
				} /* while there are elements in the collision chain */
				*previousP = sentinel;
			} /* for each slot of the x subtable */
		} else {		/* resize xlist */
			DdNode *h = NULL;
			DdNodePtr *newxlist;
			unsigned int newxslots;
			int newxshift;
			/* Empty current xlist. Nodes that stay go to list h;
			** nodes that move go to list g. */
			for (i = 0; i < xslots; i++) {
				f = xlist[i];
				while (f != sentinel) {
					next = f->next;
					f1 = cuddT(f); f0 = cuddE(f);
					if (f1->index != (DdHalfWord) yindex &&
					Cudd_Regular(f0)->index != (DdHalfWord) yindex) {
						/* stays */
						f->next = h;
						h = f;
						newxkeys++;
					} else {
						f->index = yindex;
						f->next = g;
						g = f;
					}
					f = next;
				} /* while there are elements in the collision chain */
			} /* for each slot of the x subtable */
			/* Decide size of new subtable. */
			newxshift = xshift;
			newxslots = xslots;
			while ((unsigned) oldxkeys > DD_MAX_SUBTABLE_DENSITY * newxslots) {
				newxshift--;
				newxslots <<= 1;
			}
			while ((unsigned) oldxkeys < newxslots &&
			newxslots > table->initSlots) {
				newxshift++;
				newxslots >>= 1;
			}
			/* Try to allocate new table. Be ready to back off. */
			saveHandler = MMoutOfMemory;
			MMoutOfMemory = table->outOfMemCallback;
			newxlist = ALLOC(DdNodePtr, newxslots);
			MMoutOfMemory = saveHandler;
			if (newxlist == NULL) {
				(void) fprintf(table->err, "Unable to resize subtable %d for lack of memory\n", i);
			} else {
				table->slots += ((int) newxslots - xslots);
				table->minDead = (unsigned)
				(table->gcFrac * (double) table->slots);
				table->cacheSlack = (int)
				ddMin(table->maxCacheHard, DD_MAX_CACHE_TO_SLOTS_RATIO
				* table->slots) - 2 * (int) table->cacheSlots;
				table->memused +=
				((int) newxslots - xslots) * sizeof(DdNodePtr);
				FREE(xlist);
				xslots =  newxslots;
				xshift = newxshift;
				xlist = newxlist;
			}
			/* Initialize new subtable. */
			for (i = 0; i < xslots; i++) {
				xlist[i] = sentinel;
			}
			/* Move nodes that were parked in list h to their new home. */
			f = h;
			while (f != NULL) {
				next = f->next;
				f1 = cuddT(f);
				f0 = cuddE(f);
				/* Check xlist for pair (f11,f01). */
				posn = ddHash(f1, f0, xshift);
				/* For each element tmp in collision list xlist[posn]. */
				previousP = &(xlist[posn]);
				tmp = *previousP;
				while (f1 < cuddT(tmp)) {
					previousP = &(tmp->next);
					tmp = *previousP;
				}
				while (f1 == cuddT(tmp) && f0 < cuddE(tmp)) {
					previousP = &(tmp->next);
					tmp = *previousP;
				}
				f->next = *previousP;
				*previousP = f;
				f = next;
			}
		}

#ifdef DD_COUNT
		table->swapSteps += oldxkeys - newxkeys;
#endif
		/* Take care of the x nodes that must be re-expressed.
		** They form a linked list pointed by g. Their index has been
		** already changed to yindex.
		*/
		f = g;
		while (f != NULL) {
			next = f->next;
			/* Find f1, f0, f11, f10, f01, f00. */
			f1 = cuddT(f);
#ifdef DD_DEBUG
			assert(!(Cudd_IsComplement(f1)));
#endif
			/* Before swap: f are decomposed by davio expansion,
			** while f1, f0 are decomposed by shannon expansions.
			** After swap: f are decomposed by shannon expansions,
			** while newf1, newf0 are decomposed by davio expansion.
			*/
			if ((int) f1->index == yindex) {
				f11 = cuddT(f1); f10 = cuddE(f1);
			} else {
				f11 = f10 = f1;
			}
#ifdef DD_DEBUG
			assert(!(Cudd_IsComplement(f11)));
#endif
			f0 = cuddE(f);
			comple = Cudd_IsComplement(f0);
			f0 = Cudd_Regular(f0);
			if ((int) f0->index == yindex) {
				f01 = cuddT(f0); f00 = cuddE(f0);
			} else {
				f01 = f00 = f0;
			}
			if (comple) {
				f01 = Cudd_Not(f01);
				f00 = Cudd_Not(f00);
			}
			/* Decrease ref count of f1. */
			cuddSatDec(f1->ref);
			/* Create the new T child. */
			if (f01 == Cudd_Not(DD_ONE(table))) {
				newf1 = f11;
				cuddSatInc(newf1->ref);
			} else {
				/* Check xlist for triple (xindex,f11,f01). */
				posn = ddHash(f11, f01, xshift);
				/* For each element newf1 in collision list xlist[posn]. */
				previousP = &(xlist[posn]);
				newf1 = *previousP;
				while (f11 < cuddT(newf1)) {
					previousP = &(newf1->next);
					newf1 = *previousP;
				}
				while (f11 == cuddT(newf1) && f01 < cuddE(newf1)) {
					previousP = &(newf1->next);
					newf1 = *previousP;
				}
				if (cuddT(newf1) == f11 && cuddE(newf1) == f01) {
					cuddSatInc(newf1->ref);
				} else { /* no match */
					newf1 = cuddDynamicAllocNode(table);
					if (newf1 == NULL) goto cuddSwapOutOfMem;
					newf1->index = xindex; newf1->ref = 1;
					cuddT(newf1) = f11;
					cuddE(newf1) = f01;
					/* Insert newf1 in the collision list xlist[posn];
					** increase the ref counts of f11 and f01.
					*/
					newxkeys++;
					newf1->next = *previousP;
					*previousP = newf1;
					cuddSatInc(f11->ref);
					tmp = Cudd_Regular(f01);
					cuddSatInc(tmp->ref);
				}
			}
			cuddT(f) = newf1;
#ifdef DD_DEBUG
			assert(!(Cudd_IsComplement(newf1)));
#endif

			/* Do the same for f0, keeping complement dots into account. */
			/* Decrease ref count of f0. */
			tmp = Cudd_Regular(f0);
			cuddSatDec(tmp->ref);
			/* Create the new E child. */
			if (f00 == Cudd_Not(DD_ONE(table))) {
				newf0 = f10;
				tmp = Cudd_Regular(newf0);
				cuddSatInc(tmp->ref);
			} else {
				/* make sure f10 is regular */
				newcomplement = Cudd_IsComplement(f10);
				if (newcomplement) {
					f10 = Cudd_Not(f10);
				}
				/* Check xlist for triple (xindex,f10,f00). */
				posn = ddHash(f10, f00, xshift);
				/* For each element newf0 in collision list xlist[posn]. */
				previousP = &(xlist[posn]);
				newf0 = *previousP;
				while (f10 < cuddT(newf0)) {
					previousP = &(newf0->next);
					newf0 = *previousP;
				}
				while (f10 == cuddT(newf0) && f00 < cuddE(newf0)) {
					previousP = &(newf0->next);
					newf0 = *previousP;
				}
				if (cuddT(newf0) == f10 && cuddE(newf0) == f00) {
					cuddSatInc(newf0->ref);
				} else { /* no match */
					newf0 = cuddDynamicAllocNode(table);
					if (newf0 == NULL) goto cuddSwapOutOfMem;
					newf0->index = xindex; newf0->ref = 1;
					cuddT(newf0) = f10;
					cuddE(newf0) = f00;
					/* Insert newf0 in the collision list xlist[posn];
					** increase the ref counts of f10 and f00.
					*/
					newxkeys++;
					newf0->next = *previousP;
					*previousP = newf0;
					cuddSatInc(f10->ref);
					tmp = Cudd_Regular(f00);
					cuddSatInc(tmp->ref);
				}
				if (newcomplement) {
					newf0 = Cudd_Not(newf0);
				}
			}
			cuddE(f) = newf0;

			/* Insert the modified f in ylist.
			** The modified f does not already exists in ylist.
			** (Because of the uniqueness of the cofactors.)
			*/
			posn = ddHash(newf1, newf0, yshift);
			newykeys++;
			previousP = &(ylist[posn]);
			tmp = *previousP;
			while (newf1 < cuddT(tmp)) {
				previousP = &(tmp->next);
				tmp = *previousP;
			}
			while (newf1 == cuddT(tmp) && newf0 < cuddE(tmp)) {
				previousP = &(tmp->next);
				tmp = *previousP;
			}
			f->next = *previousP;
			*previousP = f;
			f = next;
		} /* while f != NULL */

		/* GC the y layer. */

		/* For each node f in ylist. */
		for (i = 0; i < yslots; i++) {
			previousP = &(ylist[i]);
			f = *previousP;
			while (f != sentinel) {
				next = f->next;
				if (f->ref == 0) {
					tmp = cuddT(f);
					cuddSatDec(tmp->ref);
					tmp = Cudd_Regular(cuddE(f));
					cuddSatDec(tmp->ref);
					cuddDeallocNode(table,f);
					newykeys--;
				} else {
					*previousP = f;
					previousP = &(f->next);
				}
				f = next;
			} /* while f */
			*previousP = sentinel;
		} /* for i */

#ifdef DD_DEBUG
		count = 0;
		idcheck = 0;
		for (i = 0; i < yslots; i++) {
			f = ylist[i];
			while (f != sentinel) {
				count++;
				if (f->index != (DdHalfWord) yindex)
					idcheck++;
				f = f->next;
			}
		}
		if (count != newykeys) {
			(void) fprintf(table->out,
			"Error in finding newykeys\toldykeys = %d\tnewykeys = %d\tactual = %d\n",
			oldykeys,newykeys,count);
		}
		if (idcheck != 0)
			(void) fprintf(table->out,
			"Error in id's of ylist\twrong id's = %d\n",
			idcheck);
		count = 0;
		idcheck = 0;
		for (i = 0; i < xslots; i++) {
			f = xlist[i];
			while (f != sentinel) {
				count++;
				if (f->index != (DdHalfWord) xindex)
					idcheck++;
				f = f->next;
			}
		}
		if (count != newxkeys) {
			(void) fprintf(table->out,
			"Error in finding newxkeys\toldxkeys = %d \tnewxkeys = %d \tactual = %d\n",
			oldxkeys,newxkeys,count);
		}
		if (idcheck != 0)
			(void) fprintf(table->out,
			"Error in id's of xlist\twrong id's = %d\n",
			idcheck);
#endif

		isolated += (Cudd_Regular(table->vars[xindex])->ref == 1) +
		(Cudd_Regular(table->vars[yindex])->ref == 1);
		table->isolated += (unsigned int) isolated;
	}

	/* Set the appropriate fields in table. */
	table->subtables[x].nodelist = ylist;
	table->subtables[x].slots = yslots;
	table->subtables[x].shift = yshift;
	table->subtables[x].keys = newykeys;
	table->subtables[x].maxKeys = yslots * DD_MAX_SUBTABLE_DENSITY;
	i = table->subtables[x].bindVar;
	table->subtables[x].bindVar = table->subtables[y].bindVar;
	table->subtables[y].bindVar = i;
	/* Adjust fields for lazy sifting. */
	varType = table->subtables[x].varType;
	table->subtables[x].varType = table->subtables[y].varType;
	table->subtables[y].varType = varType;
	i = table->subtables[x].pairIndex;
	table->subtables[x].pairIndex = table->subtables[y].pairIndex;
	table->subtables[y].pairIndex = i;
	i = table->subtables[x].varHandled;
	table->subtables[x].varHandled = table->subtables[y].varHandled;
	table->subtables[y].varHandled = i;
	groupType = table->subtables[x].varToBeGrouped;
	table->subtables[x].varToBeGrouped = table->subtables[y].varToBeGrouped;
	table->subtables[y].varToBeGrouped = groupType;

	table->subtables[y].nodelist = xlist;
	table->subtables[y].slots = xslots;
	table->subtables[y].shift = xshift;
	table->subtables[y].keys = newxkeys;
	table->subtables[y].maxKeys = xslots * DD_MAX_SUBTABLE_DENSITY;

	table->perm[xindex] = y; table->perm[yindex] = x;
	table->invperm[x] = yindex; table->invperm[y] = xindex;

	table->keys += newxkeys + newykeys - oldxkeys - oldykeys;

	return((int)(table->keys - table->isolated));

cuddSwapOutOfMem:
	(void) fprintf(table->err,"Error: Bkfdd_D_S_SwapInPlace out of memory\n");

	return (0);

} /* end of Bkfdd_D_S_SwapInPlace */


/**
	@brief Swaps two D-D adjacent variables.

	@details It assumes that no dead nodes are present on entry to this
	procedure.  The procedure then guarantees that no dead nodes will be
	present when it terminates.  Bkfdd_D_D_SwapInPlace assumes that x &lt; y.
	It will alter the expansion-array, change D-D to D-D.

  Expansion types won't be checked inside the algorithm,
	make sure x with D, y with D before swapping.

	@return the number of keys in the table if successful; 0 otherwise.

	@sideeffect None

	In the following, use f1 to denote low-successor of f, f0 to denote
	high-successor of f.

*/
static int
Bkfdd_D_D_SwapInPlace(
  DdManager * table,
  int x,
  int y)
{
	DdNodePtr *xlist, *ylist;
	int xindex, yindex;
	int xslots, yslots;
	int xshift, yshift;
	int oldxkeys, oldykeys;
	int newxkeys, newykeys;
	int comple, newcomplement;
	int i;
	Cudd_VariableType varType;
	Cudd_LazyGroupType groupType;
	int posn;
	int isolated;
	DdNode *f,*f0,*f1,*f01,*f00,*f11,*f10,*newf1,*newf0;
	DdNode *g,*next;
	DdNodePtr *previousP;
	DdNode *tmp;
	DdNode *sentinel = &(table->sentinel);
	extern DD_OOMFP MMoutOfMemory;
	DD_OOMFP saveHandler;

#ifdef DD_DEBUG
	int    count,idcheck;
#endif

#ifdef DD_DEBUG
	assert(x < y);
	assert(cuddNextHigh(table,x) == y);
	assert(table->subtables[x].keys != 0);
	assert(table->subtables[y].keys != 0);
	assert(table->subtables[x].dead == 0);
	assert(table->subtables[y].dead == 0);
#endif

	table->ddTotalNumberSwapping++;

	/* Get parameters of x subtable. */
	xindex = table->invperm[x];
	xlist = table->subtables[x].nodelist;
	oldxkeys = table->subtables[x].keys;
	xslots = table->subtables[x].slots;
	xshift = table->subtables[x].shift;

	/* Get parameters of y subtable. */
	yindex = table->invperm[y];
	ylist = table->subtables[y].nodelist;
	oldykeys = table->subtables[y].keys;
	yslots = table->subtables[y].slots;
	yshift = table->subtables[y].shift;

	if (!cuddTestInteract(table,xindex,yindex)) {
#ifdef DD_STATS
		table->totalNISwaps++;
#endif
		newxkeys = oldxkeys;
		newykeys = oldykeys;
	} else {
		newxkeys = 0;
		newykeys = oldykeys;

		/* Check whether the two projection functions involved in this
		** swap are isolated. At the end, we'll be able to tell how many
		** isolated projection functions are there by checking only these
		** two functions again. This is done to eliminate the isolated
		** projection functions from the node count.
		*/
		isolated = - ((Cudd_Regular(table->vars[xindex])->ref == 1) +
		(Cudd_Regular(table->vars[yindex])->ref == 1));

		/* The nodes in the x layer that do not depend on
		** y will stay there; the others are put in a chain.
		** The chain is handled as a LIFO; g points to the beginning.
		*/
		g = NULL;
		if ((oldxkeys >= xslots || (unsigned) xslots == table->initSlots) &&
		oldxkeys <= DD_MAX_SUBTABLE_DENSITY * xslots) {
			for (i = 0; i < xslots; i++) {
				previousP = &(xlist[i]);
				f = *previousP;
				while (f != sentinel) {
					next = f->next;
					f1 = cuddT(f); f0 = cuddE(f);
					if (f1->index != (DdHalfWord) yindex &&
					Cudd_Regular(f0)->index != (DdHalfWord) yindex) {
						/* stays */
						newxkeys++;
						*previousP = f;
						previousP = &(f->next);
					} else {
						f->index = yindex;
						f->next = g;
						g = f;
					}
					f = next;
				} /* while there are elements in the collision chain */
				*previousP = sentinel;
			} /* for each slot of the x subtable */
		} else {		/* resize xlist */
			DdNode *h = NULL;
			DdNodePtr *newxlist;
			unsigned int newxslots;
			int newxshift;
			/* Empty current xlist. Nodes that stay go to list h;
			** nodes that move go to list g. */
			for (i = 0; i < xslots; i++) {
				f = xlist[i];
				while (f != sentinel) {
					next = f->next;
					f1 = cuddT(f); f0 = cuddE(f);
					if (f1->index != (DdHalfWord) yindex &&
					Cudd_Regular(f0)->index != (DdHalfWord) yindex) {
						/* stays */
						f->next = h;
						h = f;
						newxkeys++;
					} else {
						f->index = yindex;
						f->next = g;
						g = f;
					}
					f = next;
				} /* while there are elements in the collision chain */
			} /* for each slot of the x subtable */
			/* Decide size of new subtable. */
			newxshift = xshift;
			newxslots = xslots;
			while ((unsigned) oldxkeys > DD_MAX_SUBTABLE_DENSITY * newxslots) {
				newxshift--;
				newxslots <<= 1;
			}
			while ((unsigned) oldxkeys < newxslots &&
			newxslots > table->initSlots) {
				newxshift++;
				newxslots >>= 1;
			}
			/* Try to allocate new table. Be ready to back off. */
			saveHandler = MMoutOfMemory;
			MMoutOfMemory = table->outOfMemCallback;
			newxlist = ALLOC(DdNodePtr, newxslots);
			MMoutOfMemory = saveHandler;
			if (newxlist == NULL) {
				(void) fprintf(table->err, "Unable to resize subtable %d for lack of memory\n", i);
			} else {
				table->slots += ((int) newxslots - xslots);
				table->minDead = (unsigned)
				(table->gcFrac * (double) table->slots);
				table->cacheSlack = (int)
				ddMin(table->maxCacheHard, DD_MAX_CACHE_TO_SLOTS_RATIO
				* table->slots) - 2 * (int) table->cacheSlots;
				table->memused +=
				((int) newxslots - xslots) * sizeof(DdNodePtr);
				FREE(xlist);
				xslots =  newxslots;
				xshift = newxshift;
				xlist = newxlist;
			}
			/* Initialize new subtable. */
			for (i = 0; i < xslots; i++) {
				xlist[i] = sentinel;
			}
			/* Move nodes that were parked in list h to their new home. */
			f = h;
			while (f != NULL) {
				next = f->next;
				f1 = cuddT(f);
				f0 = cuddE(f);
				/* Check xlist for pair (f11,f01). */
				posn = ddHash(f1, f0, xshift);
				/* For each element tmp in collision list xlist[posn]. */
				previousP = &(xlist[posn]);
				tmp = *previousP;
				while (f1 < cuddT(tmp)) {
					previousP = &(tmp->next);
					tmp = *previousP;
				}
				while (f1 == cuddT(tmp) && f0 < cuddE(tmp)) {
					previousP = &(tmp->next);
					tmp = *previousP;
				}
				f->next = *previousP;
				*previousP = f;
				f = next;
			}
		}

#ifdef DD_COUNT
		table->swapSteps += oldxkeys - newxkeys;
#endif
		/* Take care of the x nodes that must be re-expressed.
		** They form a linked list pointed by g. Their index has been
		** already changed to yindex.
		*/
		f = g;
		while (f != NULL) {
			next = f->next;
			/* Find f1, f0, f11, f10, f01, f00. */
			f1 = cuddT(f);
#ifdef DD_DEBUG
			assert(!(Cudd_IsComplement(f1)));
#endif
			/* Before swap: f are decomposed by davio expansion,
			** while f1, f0 are decomposed by davio expansions.
			** After swap: f are decomposed by davio expansions,
			** while newf1, newf0 are decomposed by davio expansion.
			*/
			if ((int) f1->index == yindex) {
				f11 = cuddT(f1); f10 = cuddE(f1);
			} else {
				f11 = f1;
				f10 = Cudd_Not(DD_ONE(table));
			}
#ifdef DD_DEBUG
			assert(!(Cudd_IsComplement(f11)));
#endif
			f0 = cuddE(f);
			comple = Cudd_IsComplement(f0);
			f0 = Cudd_Regular(f0);
			if ((int) f0->index == yindex) {
				f01 = cuddT(f0); f00 = cuddE(f0);
			} else {
				f01 = f0;
				f00 = Cudd_Not(DD_ONE(table));
			}
			if (comple) {
				f01 = Cudd_Not(f01);
			}
			/* Decrease ref count of f1. */
			cuddSatDec(f1->ref);
			/* Create the new T child. */
			if (f01 == Cudd_Not(DD_ONE(table))) {
				newf1 = f11;
				cuddSatInc(newf1->ref);
			} else {
				/* Check xlist for triple (xindex,f11,f01). */
				posn = ddHash(f11, f01, xshift);
				/* For each element newf1 in collision list xlist[posn]. */
				previousP = &(xlist[posn]);
				newf1 = *previousP;
				while (f11 < cuddT(newf1)) {
					previousP = &(newf1->next);
					newf1 = *previousP;
				}
				while (f11 == cuddT(newf1) && f01 < cuddE(newf1)) {
					previousP = &(newf1->next);
					newf1 = *previousP;
				}
				if (cuddT(newf1) == f11 && cuddE(newf1) == f01) {
					cuddSatInc(newf1->ref);
				} else { /* no match */
					newf1 = cuddDynamicAllocNode(table);
					if (newf1 == NULL) goto cuddSwapOutOfMem;
					newf1->index = xindex; newf1->ref = 1;
					cuddT(newf1) = f11;
					cuddE(newf1) = f01;
					/* Insert newf1 in the collision list xlist[posn];
					** increase the ref counts of f11 and f01.
					*/
					newxkeys++;
					newf1->next = *previousP;
					*previousP = newf1;
					cuddSatInc(f11->ref);
					tmp = Cudd_Regular(f01);
					cuddSatInc(tmp->ref);
				}
			}
			cuddT(f) = newf1;
#ifdef DD_DEBUG
			assert(!(Cudd_IsComplement(newf1)));
#endif

			/* Do the same for f0, keeping complement dots into account. */
			/* Decrease ref count of f0. */
			tmp = Cudd_Regular(f0);
			cuddSatDec(tmp->ref);
			/* Create the new E child. */
			if (f00 == Cudd_Not(DD_ONE(table))) {
				newf0 = f10;
				tmp = Cudd_Regular(newf0);
				cuddSatInc(tmp->ref);
			} else {
				/* make sure f10 is regular */
				newcomplement = Cudd_IsComplement(f10);
				if (newcomplement) {
					f10 = Cudd_Not(f10);
				}
				/* Check xlist for triple (xindex,f10,f00). */
				posn = ddHash(f10, f00, xshift);
				/* For each element newf0 in collision list xlist[posn]. */
				previousP = &(xlist[posn]);
				newf0 = *previousP;
				while (f10 < cuddT(newf0)) {
					previousP = &(newf0->next);
					newf0 = *previousP;
				}
				while (f10 == cuddT(newf0) && f00 < cuddE(newf0)) {
					previousP = &(newf0->next);
					newf0 = *previousP;
				}
				if (cuddT(newf0) == f10 && cuddE(newf0) == f00) {
					cuddSatInc(newf0->ref);
				} else { /* no match */
					newf0 = cuddDynamicAllocNode(table);
					if (newf0 == NULL) goto cuddSwapOutOfMem;
					newf0->index = xindex; newf0->ref = 1;
					cuddT(newf0) = f10;
					cuddE(newf0) = f00;
					/* Insert newf0 in the collision list xlist[posn];
					** increase the ref counts of f10 and f00.
					*/
					newxkeys++;
					newf0->next = *previousP;
					*previousP = newf0;
					cuddSatInc(f10->ref);
					tmp = Cudd_Regular(f00);
					cuddSatInc(tmp->ref);
				}
				if (newcomplement) {
					newf0 = Cudd_Not(newf0);
				}
			}
			cuddE(f) = newf0;

			/* Insert the modified f in ylist.
			** The modified f does not already exists in ylist.
			** (Because of the uniqueness of the cofactors.)
			*/
			posn = ddHash(newf1, newf0, yshift);
			newykeys++;
			previousP = &(ylist[posn]);
			tmp = *previousP;
			while (newf1 < cuddT(tmp)) {
				previousP = &(tmp->next);
				tmp = *previousP;
			}
			while (newf1 == cuddT(tmp) && newf0 < cuddE(tmp)) {
				previousP = &(tmp->next);
				tmp = *previousP;
			}
			f->next = *previousP;
			*previousP = f;
			f = next;
		} /* while f != NULL */

		/* GC the y layer. */

		/* For each node f in ylist. */
		for (i = 0; i < yslots; i++) {
			previousP = &(ylist[i]);
			f = *previousP;
			while (f != sentinel) {
				next = f->next;
				if (f->ref == 0) {
					tmp = cuddT(f);
					cuddSatDec(tmp->ref);
					tmp = Cudd_Regular(cuddE(f));
					cuddSatDec(tmp->ref);
					cuddDeallocNode(table,f);
					newykeys--;
				} else {
					*previousP = f;
					previousP = &(f->next);
				}
				f = next;
			} /* while f */
			*previousP = sentinel;
		} /* for i */

#ifdef DD_DEBUG
		count = 0;
		idcheck = 0;
		for (i = 0; i < yslots; i++) {
			f = ylist[i];
			while (f != sentinel) {
				count++;
				if (f->index != (DdHalfWord) yindex)
					idcheck++;
				f = f->next;
			}
		}
		if (count != newykeys) {
			(void) fprintf(table->out,
			"Error in finding newykeys\toldykeys = %d\tnewykeys = %d\tactual = %d\n",
			oldykeys,newykeys,count);
		}
		if (idcheck != 0)
			(void) fprintf(table->out,
			"Error in id's of ylist\twrong id's = %d\n",
			idcheck);
		count = 0;
		idcheck = 0;
		for (i = 0; i < xslots; i++) {
			f = xlist[i];
			while (f != sentinel) {
				count++;
				if (f->index != (DdHalfWord) xindex)
					idcheck++;
				f = f->next;
			}
		}
		if (count != newxkeys) {
			(void) fprintf(table->out,
			"Error in finding newxkeys\toldxkeys = %d \tnewxkeys = %d \tactual = %d\n",
			oldxkeys,newxkeys,count);
		}
		if (idcheck != 0)
			(void) fprintf(table->out,
			"Error in id's of xlist\twrong id's = %d\n",
			idcheck);
#endif

		isolated += (Cudd_Regular(table->vars[xindex])->ref == 1) +
		(Cudd_Regular(table->vars[yindex])->ref == 1);
		table->isolated += (unsigned int) isolated;
	}

	/* Set the appropriate fields in table. */
	table->subtables[x].nodelist = ylist;
	table->subtables[x].slots = yslots;
	table->subtables[x].shift = yshift;
	table->subtables[x].keys = newykeys;
	table->subtables[x].maxKeys = yslots * DD_MAX_SUBTABLE_DENSITY;
	i = table->subtables[x].bindVar;
	table->subtables[x].bindVar = table->subtables[y].bindVar;
	table->subtables[y].bindVar = i;
	/* Adjust fields for lazy sifting. */
	varType = table->subtables[x].varType;
	table->subtables[x].varType = table->subtables[y].varType;
	table->subtables[y].varType = varType;
	i = table->subtables[x].pairIndex;
	table->subtables[x].pairIndex = table->subtables[y].pairIndex;
	table->subtables[y].pairIndex = i;
	i = table->subtables[x].varHandled;
	table->subtables[x].varHandled = table->subtables[y].varHandled;
	table->subtables[y].varHandled = i;
	groupType = table->subtables[x].varToBeGrouped;
	table->subtables[x].varToBeGrouped = table->subtables[y].varToBeGrouped;
	table->subtables[y].varToBeGrouped = groupType;

	table->subtables[y].nodelist = xlist;
	table->subtables[y].slots = xslots;
	table->subtables[y].shift = xshift;
	table->subtables[y].keys = newxkeys;
	table->subtables[y].maxKeys = xslots * DD_MAX_SUBTABLE_DENSITY;

	table->perm[xindex] = y; table->perm[yindex] = x;
	table->invperm[x] = yindex; table->invperm[y] = xindex;
	
	table->keys += newxkeys + newykeys - oldxkeys - oldykeys;

	return((int)(table->keys - table->isolated));

cuddSwapOutOfMem:
	(void) fprintf(table->err,"Error: Bkfdd_D_D_SwapInPlace out of memory\n");

	return (0);

} /* end of Bkfdd_D_D_SwapInPlace */


/** Naive version of swapping two adjacent variables.
 **	Interact matrix is invalid in these functions.
 ** These functions are mostly used in BKFDD's OET-sifting, an extension
 ** of KFDD's DTL-sifting.
*/

/**
  @brief Swaps two S-S adjacent variables.
  @sideeffect None

*/
int
naive_S_S_Swap(
  DdManager * table,
  int  x,
  int  y)
{
	DdNodePtr *xlist, *ylist;
	int    xindex, yindex;
	int    xslots, yslots;
	int    xshift, yshift;
	int    oldxkeys, oldykeys;
	int    newxkeys, newykeys;
	int    comple, newcomplement;
	int    i;
	Cudd_VariableType varType;
	Cudd_LazyGroupType groupType;
	int    posn;
	int    isolated;
	DdNode *f,*f0,*f1,*f01,*f00,*f11,*f10,*newf1,*newf0;
	DdNode *g,*next;
	DdNodePtr *previousP;
	DdNode *tmp;
	DdNode *sentinel = &(table->sentinel);
	extern DD_OOMFP MMoutOfMemory;
	DD_OOMFP saveHandler;

#ifdef DD_DEBUG
	int    count,idcheck;
#endif

#ifdef DD_DEBUG
	assert(x < y);
	assert(cuddNextHigh(table,x) == y);
	assert(table->subtables[x].keys != 0);
	assert(table->subtables[y].keys != 0);
	assert(table->subtables[x].dead == 0);
	assert(table->subtables[y].dead == 0);
#endif

	table->ddTotalNumberSwapping++;

	/* Get parameters of x subtable. */
	xindex = table->invperm[x];
	xlist = table->subtables[x].nodelist;
	oldxkeys = table->subtables[x].keys;
	xslots = table->subtables[x].slots;
	xshift = table->subtables[x].shift;

	/* Get parameters of y subtable. */
	yindex = table->invperm[y];
	ylist = table->subtables[y].nodelist;
	oldykeys = table->subtables[y].keys;
	yslots = table->subtables[y].slots;
	yshift = table->subtables[y].shift;

	newxkeys = 0;
	newykeys = oldykeys;

	isolated = - ((Cudd_Regular(table->vars[xindex])->ref == 1) +
	(Cudd_Regular(table->vars[yindex])->ref == 1));

	/* The nodes in the x layer that do not depend on
	** y will stay there; the others are put in a chain.
	** The chain is handled as a LIFO; g points to the beginning.
	*/
	g = NULL;
	if ((oldxkeys >= xslots || (unsigned) xslots == table->initSlots) &&
	oldxkeys <= DD_MAX_SUBTABLE_DENSITY * xslots) {
		for (i = 0; i < xslots; i++) {
			previousP = &(xlist[i]);
			f = *previousP;
			while (f != sentinel) {
				next = f->next;
				f1 = cuddT(f); f0 = cuddE(f);
				if (f1->index != (DdHalfWord) yindex &&
				Cudd_Regular(f0)->index != (DdHalfWord) yindex) {
					/* stays */
					newxkeys++;
					*previousP = f;
					previousP = &(f->next);
				} else {
					f->index = yindex;
					f->next = g;
					g = f;
				}
				f = next;
			} /* while there are elements in the collision chain */
			*previousP = sentinel;
		} /* for each slot of the x subtable */
	} else {		/* resize xlist */
		DdNode *h = NULL;
		DdNodePtr *newxlist;
		unsigned int newxslots;
		int newxshift;
		/* Empty current xlist. Nodes that stay go to list h;
		** nodes that move go to list g. */
		for (i = 0; i < xslots; i++) {
			f = xlist[i];
			while (f != sentinel) {
				next = f->next;
				f1 = cuddT(f); f0 = cuddE(f);
				if (f1->index != (DdHalfWord) yindex &&
				Cudd_Regular(f0)->index != (DdHalfWord) yindex) {
					/* stays */
					f->next = h;
					h = f;
					newxkeys++;
				} else {
					f->index = yindex;
					f->next = g;
					g = f;
				}
				f = next;
			} /* while there are elements in the collision chain */
		} /* for each slot of the x subtable */
		/* Decide size of new subtable. */
		newxshift = xshift;
		newxslots = xslots;
		while ((unsigned) oldxkeys > DD_MAX_SUBTABLE_DENSITY * newxslots) {
			newxshift--;
			newxslots <<= 1;
		}
		while ((unsigned) oldxkeys < newxslots &&
		newxslots > table->initSlots) {
			newxshift++;
			newxslots >>= 1;
		}
		/* Try to allocate new table. Be ready to back off. */
		saveHandler = MMoutOfMemory;
		MMoutOfMemory = table->outOfMemCallback;
		newxlist = ALLOC(DdNodePtr, newxslots);
		MMoutOfMemory = saveHandler;
		if (newxlist == NULL) {
			(void) fprintf(table->err, "Unable to resize subtable %d for lack of memory\n", i);
		} else {
			table->slots += ((int) newxslots - xslots);
			table->minDead = (unsigned)
			(table->gcFrac * (double) table->slots);
			table->cacheSlack = (int)
			ddMin(table->maxCacheHard, DD_MAX_CACHE_TO_SLOTS_RATIO
			* table->slots) - 2 * (int) table->cacheSlots;
			table->memused +=
			((int) newxslots - xslots) * sizeof(DdNodePtr);
			FREE(xlist);
			xslots =  newxslots;
			xshift = newxshift;
			xlist = newxlist;
		}
		/* Initialize new subtable. */
		for (i = 0; i < xslots; i++) {
			xlist[i] = sentinel;
		}
		/* Move nodes that were parked in list h to their new home. */
		f = h;
		while (f != NULL) {
			next = f->next;
			f1 = cuddT(f);
			f0 = cuddE(f);
			/* Check xlist for pair (f11,f01). */
			posn = ddHash(f1, f0, xshift);
			/* For each element tmp in collision list xlist[posn]. */
			previousP = &(xlist[posn]);
			tmp = *previousP;
			while (f1 < cuddT(tmp)) {
				previousP = &(tmp->next);
				tmp = *previousP;
			}
			while (f1 == cuddT(tmp) && f0 < cuddE(tmp)) {
				previousP = &(tmp->next);
				tmp = *previousP;
			}
			f->next = *previousP;
			*previousP = f;
			f = next;
		}
	}

#ifdef DD_COUNT
	table->swapSteps += oldxkeys - newxkeys;
#endif
	/* Take care of the x nodes that must be re-expressed.
	** They form a linked list pointed by g. Their index has been
	** already changed to yindex.
	*/
	f = g;
	while (f != NULL) {
		next = f->next;
		/* Find f1, f0, f11, f10, f01, f00. */
		f1 = cuddT(f);
#ifdef DD_DEBUG
		assert(!(Cudd_IsComplement(f1)));
#endif
		if ((int) f1->index == yindex) {
			f11 = cuddT(f1); f10 = cuddE(f1);
		} else {
			f11 = f10 = f1;
		}
#ifdef DD_DEBUG
		assert(!(Cudd_IsComplement(f11)));
#endif
		f0 = cuddE(f);
		comple = Cudd_IsComplement(f0);
		f0 = Cudd_Regular(f0);
		if ((int) f0->index == yindex) {
			f01 = cuddT(f0); f00 = cuddE(f0);
		} else {
			f01 = f00 = f0;
		}
		if (comple) {
			f01 = Cudd_Not(f01);
			f00 = Cudd_Not(f00);
		}
		/* Decrease ref count of f1. */
		cuddSatDec(f1->ref);
		/* Create the new T child. */
		if (f11 == f01) {
			newf1 = f11;
			cuddSatInc(newf1->ref);
		} else {
			/* Check xlist for triple (xindex,f11,f01). */
			posn = ddHash(f11, f01, xshift);
			/* For each element newf1 in collision list xlist[posn]. */
			previousP = &(xlist[posn]);
			newf1 = *previousP;
			while (f11 < cuddT(newf1)) {
				previousP = &(newf1->next);
				newf1 = *previousP;
			}
			while (f11 == cuddT(newf1) && f01 < cuddE(newf1)) {
				previousP = &(newf1->next);
				newf1 = *previousP;
			}
			if (cuddT(newf1) == f11 && cuddE(newf1) == f01) {
				cuddSatInc(newf1->ref);
			} else { /* no match */
				newf1 = cuddDynamicAllocNode(table);
				if (newf1 == NULL)
				goto cuddSwapOutOfMem;
				newf1->index = xindex; newf1->ref = 1;
				cuddT(newf1) = f11;
				cuddE(newf1) = f01;
				/* Insert newf1 in the collision list xlist[posn];
				** increase the ref counts of f11 and f01.
				*/
				newxkeys++;
				newf1->next = *previousP;
				*previousP = newf1;
				cuddSatInc(f11->ref);
				tmp = Cudd_Regular(f01);
				cuddSatInc(tmp->ref);
			}
		}
		cuddT(f) = newf1;
#ifdef DD_DEBUG
		assert(!(Cudd_IsComplement(newf1)));
#endif

		/* Do the same for f0, keeping complement dots into account. */
		/* Decrease ref count of f0. */
		tmp = Cudd_Regular(f0);
		cuddSatDec(tmp->ref);
		/* Create the new E child. */
		if (f10 == f00) {
			newf0 = f00;
			tmp = Cudd_Regular(newf0);
			cuddSatInc(tmp->ref);
		} else {
			/* make sure f10 is regular */
			newcomplement = Cudd_IsComplement(f10);
			if (newcomplement) {
				f10 = Cudd_Not(f10);
				f00 = Cudd_Not(f00);
			}
			/* Check xlist for triple (xindex,f10,f00). */
			posn = ddHash(f10, f00, xshift);
			/* For each element newf0 in collision list xlist[posn]. */
			previousP = &(xlist[posn]);
			newf0 = *previousP;
			while (f10 < cuddT(newf0)) {
				previousP = &(newf0->next);
				newf0 = *previousP;
			}
			while (f10 == cuddT(newf0) && f00 < cuddE(newf0)) {
				previousP = &(newf0->next);
				newf0 = *previousP;
			}
			if (cuddT(newf0) == f10 && cuddE(newf0) == f00) {
				cuddSatInc(newf0->ref);
			} else { /* no match */
				newf0 = cuddDynamicAllocNode(table);
				if (newf0 == NULL)
				goto cuddSwapOutOfMem;
				newf0->index = xindex; newf0->ref = 1;
				cuddT(newf0) = f10;
				cuddE(newf0) = f00;
				/* Insert newf0 in the collision list xlist[posn];
				** increase the ref counts of f10 and f00.
				*/
				newxkeys++;
				newf0->next = *previousP;
				*previousP = newf0;
				cuddSatInc(f10->ref);
				tmp = Cudd_Regular(f00);
				cuddSatInc(tmp->ref);
			}
			if (newcomplement) {
				newf0 = Cudd_Not(newf0);
			}
		}
		cuddE(f) = newf0;

		/* Insert the modified f in ylist.
		** The modified f does not already exists in ylist.
		** (Because of the uniqueness of the cofactors.)
		*/
		posn = ddHash(newf1, newf0, yshift);
		newykeys++;
		previousP = &(ylist[posn]);
		tmp = *previousP;
		while (newf1 < cuddT(tmp)) {
			previousP = &(tmp->next);
			tmp = *previousP;
		}
		while (newf1 == cuddT(tmp) && newf0 < cuddE(tmp)) {
			previousP = &(tmp->next);
			tmp = *previousP;
		}
		f->next = *previousP;
		*previousP = f;
		f = next;
	} /* while f != NULL */

	/* GC the y layer. */

	/* For each node f in ylist. */
	for (i = 0; i < yslots; i++) {
		previousP = &(ylist[i]);
		f = *previousP;
		while (f != sentinel) {
			next = f->next;
			if (f->ref == 0) {
				tmp = cuddT(f);
				cuddSatDec(tmp->ref);
				tmp = Cudd_Regular(cuddE(f));
				cuddSatDec(tmp->ref);
				cuddDeallocNode(table,f);
				newykeys--;
			} else {
				*previousP = f;
				previousP = &(f->next);
			}
			f = next;
		} /* while f */
		*previousP = sentinel;
	} /* for i */

#ifdef DD_DEBUG
	count = 0;
	idcheck = 0;
	for (i = 0; i < yslots; i++) {
		f = ylist[i];
		while (f != sentinel) {
			count++;
			if (f->index != (DdHalfWord) yindex)
			idcheck++;
			f = f->next;
		}
	}
	if (count != newykeys) {
		(void) fprintf(table->out,
		"Error in finding newykeys\toldykeys = %d\tnewykeys = %d\tactual = %d\n",
		oldykeys,newykeys,count);
	}
	if (idcheck != 0)
	(void) fprintf(table->out,
	"Error in id's of ylist\twrong id's = %d\n",
	idcheck);
	count = 0;
	idcheck = 0;
	for (i = 0; i < xslots; i++) {
		f = xlist[i];
		while (f != sentinel) {
			count++;
			if (f->index != (DdHalfWord) xindex)
			idcheck++;
			f = f->next;
		}
	}
	if (count != newxkeys) {
		(void) fprintf(table->out,
		"Error in finding newxkeys\toldxkeys = %d \tnewxkeys = %d \tactual = %d\n",
		oldxkeys,newxkeys,count);
	}
	if (idcheck != 0)
		(void) fprintf(table->out,
		"Error in id's of xlist\twrong id's = %d\n",
		idcheck);
#endif

	isolated += (Cudd_Regular(table->vars[xindex])->ref == 1) +
	(Cudd_Regular(table->vars[yindex])->ref == 1);

	table->isolated += (unsigned int) isolated;

	/* Set the appropriate fields in table. */
	table->subtables[x].nodelist = ylist;
	table->subtables[x].slots = yslots;
	table->subtables[x].shift = yshift;
	table->subtables[x].keys = newykeys;
	table->subtables[x].maxKeys = yslots * DD_MAX_SUBTABLE_DENSITY;

	i = table->subtables[x].bindVar;
	table->subtables[x].bindVar = table->subtables[y].bindVar;
	table->subtables[y].bindVar = i;
	/* Adjust fields for lazy sifting. */
	varType = table->subtables[x].varType;
	table->subtables[x].varType = table->subtables[y].varType;
	table->subtables[y].varType = varType;
	i = table->subtables[x].pairIndex;
	table->subtables[x].pairIndex = table->subtables[y].pairIndex;
	table->subtables[y].pairIndex = i;
	i = table->subtables[x].varHandled;
	table->subtables[x].varHandled = table->subtables[y].varHandled;
	table->subtables[y].varHandled = i;
	groupType = table->subtables[x].varToBeGrouped;
	table->subtables[x].varToBeGrouped = table->subtables[y].varToBeGrouped;
	table->subtables[y].varToBeGrouped = groupType;

	table->subtables[y].nodelist = xlist;
	table->subtables[y].slots = xslots;
	table->subtables[y].shift = xshift;
	table->subtables[y].keys = newxkeys;
	table->subtables[y].maxKeys = xslots * DD_MAX_SUBTABLE_DENSITY;
	
	// adjust level-index mapping, level-expn mapping
	table->perm[xindex] = y; table->perm[yindex] = x;
	table->invperm[x] = yindex; table->invperm[y] = xindex;

	table->keys += newxkeys + newykeys - oldxkeys - oldykeys;

	return((int)(table->keys - table->isolated));

cuddSwapOutOfMem:
	(void) fprintf(table->err,"Error: naive_S_S_Swap out of memory\n");

	return (0);

} /* end of naive_S_S_Swap */


/**
	@brief Swaps two S-D adjacent variables.

*/
static int
naive_S_D_Swap(
	DdManager * table,
	int x,
	int y)
{
	DdNodePtr *xlist, *ylist;
	int xindex, yindex;
	int xslots, yslots;
	int xshift, yshift;
	int oldxkeys, oldykeys;
	int newxkeys, newykeys;
	int comple, newcomplement;
	int i;
	Cudd_VariableType varType;
	Cudd_LazyGroupType groupType;
	int posn;
	int isolated;
	DdNode *f,*f0,*f1,*f01,*f00,*f11,*f10,*newf1,*newf0;
	DdNode *g,*next;
	DdNodePtr *previousP;
	DdNode *tmp;
	DdNode *sentinel = &(table->sentinel);
	extern DD_OOMFP MMoutOfMemory;
	DD_OOMFP saveHandler;

#ifdef DD_DEBUG
	int    count,idcheck;
#endif

#ifdef DD_DEBUG
	assert(x < y);
	assert(cuddNextHigh(table,x) == y);
	assert(table->subtables[x].keys != 0);
	assert(table->subtables[y].keys != 0);
	assert(table->subtables[x].dead == 0);
	assert(table->subtables[y].dead == 0);
#endif

	table->ddTotalNumberSwapping++;

	/* Get parameters of x subtable. */
	xindex = table->invperm[x];
	xlist = table->subtables[x].nodelist;
	oldxkeys = table->subtables[x].keys;
	xslots = table->subtables[x].slots;
	xshift = table->subtables[x].shift;

	/* Get parameters of y subtable. */
	yindex = table->invperm[y];
	ylist = table->subtables[y].nodelist;
	oldykeys = table->subtables[y].keys;
	yslots = table->subtables[y].slots;
	yshift = table->subtables[y].shift;

	newxkeys = 0;
	newykeys = oldykeys;

	isolated = - ((Cudd_Regular(table->vars[xindex])->ref == 1) +
	(Cudd_Regular(table->vars[yindex])->ref == 1));

	/* The nodes in the x layer that do not depend on
	** y will stay there; the others are put in a chain.
	** The chain is handled as a LIFO; g points to the beginning.
	*/
	g = NULL;
	if ((oldxkeys >= xslots || (unsigned) xslots == table->initSlots) &&
	oldxkeys <= DD_MAX_SUBTABLE_DENSITY * xslots) {
		for (i = 0; i < xslots; i++) {
			previousP = &(xlist[i]);
			f = *previousP;
			while (f != sentinel) {
				next = f->next;
				f1 = cuddT(f); f0 = cuddE(f);
				if (f1->index != (DdHalfWord) yindex &&
				Cudd_Regular(f0)->index != (DdHalfWord) yindex) {
					/* stays */	// the function doesn't depend on yindex.
					newxkeys++;
					*previousP = f;
					previousP = &(f->next);
				} else {
					f->index = yindex;
					f->next = g;
					g = f;
				}
				f = next;
			} /* while there are elements in the collision chain */
			*previousP = sentinel;
		} /* for each slot of the x subtable */
	} else {		/* resize xlist */
		DdNode *h = NULL;
		DdNodePtr *newxlist;
		unsigned int newxslots;
		int newxshift;
		/* Empty current xlist. Nodes that stay go to list h;
		** nodes that move go to list g. */
		for (i = 0; i < xslots; i++) {
			f = xlist[i];
			while (f != sentinel) {
				next = f->next;
				f1 = cuddT(f); f0 = cuddE(f);
				if (f1->index != (DdHalfWord) yindex &&
				Cudd_Regular(f0)->index != (DdHalfWord) yindex) {
					/* stays */
					f->next = h;
					h = f;
					newxkeys++;
				} else {
					f->index = yindex;
					f->next = g;
					g = f;
				}
				f = next;
			} /* while there are elements in the collision chain */
		} /* for each slot of the x subtable */
		/* Decide size of new subtable. */
		newxshift = xshift;
		newxslots = xslots;
		while ((unsigned) oldxkeys > DD_MAX_SUBTABLE_DENSITY * newxslots) {
			newxshift--;
			newxslots <<= 1;
		}
		while ((unsigned) oldxkeys < newxslots &&
		newxslots > table->initSlots) {
			newxshift++;
			newxslots >>= 1;
		}
		/* Try to allocate new table. Be ready to back off. */
		saveHandler = MMoutOfMemory;
		MMoutOfMemory = table->outOfMemCallback;
		newxlist = ALLOC(DdNodePtr, newxslots);
		MMoutOfMemory = saveHandler;
		if (newxlist == NULL) {
			(void) fprintf(table->err, "Unable to resize subtable %d for lack of memory\n", i);
		} else {
			table->slots += ((int) newxslots - xslots);
			table->minDead = (unsigned)
			(table->gcFrac * (double) table->slots);
			table->cacheSlack = (int)
			ddMin(table->maxCacheHard, DD_MAX_CACHE_TO_SLOTS_RATIO
			* table->slots) - 2 * (int) table->cacheSlots;
			table->memused +=
			((int) newxslots - xslots) * sizeof(DdNodePtr);
			FREE(xlist);
			xslots =  newxslots;
			xshift = newxshift;
			xlist = newxlist;
		}
		/* Initialize new subtable. */
		for (i = 0; i < xslots; i++) {
			xlist[i] = sentinel;
		}
		/* Move nodes that were parked in list h to their new home. */
		f = h;
		while (f != NULL) {
			next = f->next;
			f1 = cuddT(f);
			f0 = cuddE(f);
			/* Check xlist for pair (f11,f01). */
			posn = ddHash(f1, f0, xshift);
			/* For each element tmp in collision list xlist[posn]. */
			/* Nodes in collision list are arrange in the following manner,
				For node n1, n2:  
				If n1->T > n2->T 
							then n1 > n2;
				ELse if n1->T == n2->T
							then if n1->E > n2->E 
											then n1 > n2;
				NOTE 1. Sentinel is the least element, at the rear of xlist.
			*/
			previousP = &(xlist[posn]);
			tmp = *previousP;
			while (f1 < cuddT(tmp)) {
				previousP = &(tmp->next);
				tmp = *previousP;
			}
			while (f1 == cuddT(tmp) && f0 < cuddE(tmp)) {
				previousP = &(tmp->next);
				tmp = *previousP;
			}
			f->next = *previousP;
			*previousP = f;
			f = next;
		}
	}

#ifdef DD_COUNT
	table->swapSteps += oldxkeys - newxkeys;
#endif
	/* Take care of the x nodes that must be re-expressed.
	** They form a linked list pointed by g. Their index has been
	** already changed to yindex.
	*/
	f = g;
	while (f != NULL) {
		next = f->next;
		/* Find f1, f0, f11, f10, f01, f00. */
		f1 = cuddT(f);
#ifdef DD_DEBUG
		assert(!(Cudd_IsComplement(f1)));
#endif
		/* Before swap: f are decomposed by shannon expansion,
		** while f1, f0 are decomposed by davio expansions.
		** After swap: f are decomposed by davio expansions,
		** while newf1, newf0 are decomposed by shannon expansion.
		*/
		if ((int) f1->index == yindex) {
			f11 = cuddT(f1); f10 = cuddE(f1);
		} else {
			f11 = f1;
			f10 = Cudd_Not(DD_ONE(table));
		}
#ifdef DD_DEBUG
		assert(!(Cudd_IsComplement(f11)));
#endif
		f0 = cuddE(f);
		comple = Cudd_IsComplement(f0);
		f0 = Cudd_Regular(f0);
		if ((int) f0->index == yindex) {
			f01 = cuddT(f0); f00 = cuddE(f0);
		} else {
			f01 = f0;
			f00 = Cudd_Not(DD_ONE(table));
		}
		if (comple) {
			f01 = Cudd_Not(f01);
		}
		/* Decrease ref count of f1. */
		cuddSatDec(f1->ref);
		/* Create the new T child. */
		if (f11 == f01) {
			newf1 = f11;
			cuddSatInc(newf1->ref);
		} else {
			/* Check xlist for triple (xindex,f11,f01). */
			posn = ddHash(f11, f01, xshift);
			/* For each element newf1 in collision list xlist[posn]. */
			previousP = &(xlist[posn]);
			newf1 = *previousP;
			while (f11 < cuddT(newf1)) {
				previousP = &(newf1->next);
				newf1 = *previousP;
			}
			while (f11 == cuddT(newf1) && f01 < cuddE(newf1)) {
				previousP = &(newf1->next);
				newf1 = *previousP;
			}
			if (cuddT(newf1) == f11 && cuddE(newf1) == f01) {
				cuddSatInc(newf1->ref);
			} else { /* no match */
				newf1 = cuddDynamicAllocNode(table);
				if (newf1 == NULL) goto cuddSwapOutOfMem;
				newf1->index = xindex; newf1->ref = 1;
				cuddT(newf1) = f11;
				cuddE(newf1) = f01;
				/* Insert newf1 in the collision list xlist[posn];
				** increase the ref counts of f11 and f01.
				*/
				newxkeys++;
				newf1->next = *previousP;
				*previousP = newf1;
				cuddSatInc(f11->ref);
				tmp = Cudd_Regular(f01);
				cuddSatInc(tmp->ref);
			}
		}
		cuddT(f) = newf1;
#ifdef DD_DEBUG
		assert(!(Cudd_IsComplement(newf1)));
#endif

		/* Do the same for f0, keeping complement dots into account. */
		/* Decrease ref count of f0. */
		tmp = Cudd_Regular(f0);
		cuddSatDec(tmp->ref);
		/* Create the new E child. */
		if (f10 == f00) {
			newf0 = f00;
			tmp = Cudd_Regular(newf0);
			cuddSatInc(tmp->ref);
		} else {
			/* make sure f10 is regular */
			newcomplement = Cudd_IsComplement(f10);
			if (newcomplement) {
				f10 = Cudd_Not(f10);
				f00 = Cudd_Not(f00);
			}
			/* Check xlist for triple (xindex,f10,f00). */
			posn = ddHash(f10, f00, xshift);
			/* For each element newf0 in collision list xlist[posn]. */
			previousP = &(xlist[posn]);
			newf0 = *previousP;
			while (f10 < cuddT(newf0)) {
				previousP = &(newf0->next);
				newf0 = *previousP;
			}
			while (f10 == cuddT(newf0) && f00 < cuddE(newf0)) {
				previousP = &(newf0->next);
				newf0 = *previousP;
			}
			if (cuddT(newf0) == f10 && cuddE(newf0) == f00) {
				cuddSatInc(newf0->ref);
			} else { /* no match */
				newf0 = cuddDynamicAllocNode(table);
				if (newf0 == NULL) goto cuddSwapOutOfMem;
				newf0->index = xindex; newf0->ref = 1;
				cuddT(newf0) = f10;
				cuddE(newf0) = f00;
				/* Insert newf0 in the collision list xlist[posn];
				** increase the ref counts of f10 and f00.
				*/
				newxkeys++;
				newf0->next = *previousP;
				*previousP = newf0;
				cuddSatInc(f10->ref);
				tmp = Cudd_Regular(f00);
				cuddSatInc(tmp->ref);
			}
			if (newcomplement) {
				newf0 = Cudd_Not(newf0);
			}
		}
		cuddE(f) = newf0;

		/* Insert the modified f in ylist.
		** The modified f does not already exists in ylist.
		** (Because of the uniqueness of the cofactors.)
		*/
		posn = ddHash(newf1, newf0, yshift);
		newykeys++;
		previousP = &(ylist[posn]);
		tmp = *previousP;
		while (newf1 < cuddT(tmp)) {
			previousP = &(tmp->next);
			tmp = *previousP;
		}
		while (newf1 == cuddT(tmp) && newf0 < cuddE(tmp)) {
			previousP = &(tmp->next);
			tmp = *previousP;
		}
		f->next = *previousP;
		*previousP = f;
		f = next;
	} /* while f != NULL */

	/* GC the y layer. */

	/* For each node f in ylist. */
	for (i = 0; i < yslots; i++) {
		previousP = &(ylist[i]);
		f = *previousP;
		while (f != sentinel) {
			next = f->next;
			if (f->ref == 0) {
				tmp = cuddT(f);
				cuddSatDec(tmp->ref);
				tmp = Cudd_Regular(cuddE(f));
				cuddSatDec(tmp->ref);
				cuddDeallocNode(table,f);
				newykeys--;
			} else {
				*previousP = f;
				previousP = &(f->next);
			}
			f = next;
		} /* while f */
		*previousP = sentinel;
	} /* for i */

#ifdef DD_DEBUG
	count = 0;
	idcheck = 0;
	for (i = 0; i < yslots; i++) {
		f = ylist[i];
		while (f != sentinel) {
			count++;
			if (f->index != (DdHalfWord) yindex)
				idcheck++;
			f = f->next;
		}
	}
	if (count != newykeys) {
		(void) fprintf(table->out,
		"Error in finding newykeys\toldykeys = %d\tnewykeys = %d\tactual = %d\n",
		oldykeys,newykeys,count);
	}
	if (idcheck != 0)
		(void) fprintf(table->out,
		"Error in id's of ylist\twrong id's = %d\n",
		idcheck);
	count = 0;
	idcheck = 0;
	for (i = 0; i < xslots; i++) {
		f = xlist[i];
		while (f != sentinel) {
			count++;
			if (f->index != (DdHalfWord) xindex)
				idcheck++;
			f = f->next;
		}
	}
	if (count != newxkeys) {
		(void) fprintf(table->out,
		"Error in finding newxkeys\toldxkeys = %d \tnewxkeys = %d \tactual = %d\n",
		oldxkeys,newxkeys,count);
	}
	if (idcheck != 0)
		(void) fprintf(table->out,
		"Error in id's of xlist\twrong id's = %d\n",
		idcheck);
#endif
	isolated += (Cudd_Regular(table->vars[xindex])->ref == 1) +
 (Cudd_Regular(table->vars[yindex])->ref == 1);

	table->isolated += (unsigned int) isolated;

	/* Set the appropriate fields in table. */
	table->subtables[x].nodelist = ylist;
	table->subtables[x].slots = yslots;
	table->subtables[x].shift = yshift;
	table->subtables[x].keys = newykeys;
	table->subtables[x].maxKeys = yslots * DD_MAX_SUBTABLE_DENSITY;
	i = table->subtables[x].bindVar;
	table->subtables[x].bindVar = table->subtables[y].bindVar;
	table->subtables[y].bindVar = i;
	/* Adjust fields for lazy sifting. */
	varType = table->subtables[x].varType;
	table->subtables[x].varType = table->subtables[y].varType;
	table->subtables[y].varType = varType;
	i = table->subtables[x].pairIndex;
	table->subtables[x].pairIndex = table->subtables[y].pairIndex;
	table->subtables[y].pairIndex = i;
	i = table->subtables[x].varHandled;
	table->subtables[x].varHandled = table->subtables[y].varHandled;
	table->subtables[y].varHandled = i;
	groupType = table->subtables[x].varToBeGrouped;
	table->subtables[x].varToBeGrouped = table->subtables[y].varToBeGrouped;
	table->subtables[y].varToBeGrouped = groupType;

	table->subtables[y].nodelist = xlist;
	table->subtables[y].slots = xslots;
	table->subtables[y].shift = xshift;
	table->subtables[y].keys = newxkeys;
	table->subtables[y].maxKeys = xslots * DD_MAX_SUBTABLE_DENSITY;

	table->perm[xindex] = y; table->perm[yindex] = x;
	table->invperm[x] = yindex; table->invperm[y] = xindex;

	table->keys += newxkeys + newykeys - oldxkeys - oldykeys;

	return((int)(table->keys - table->isolated));

cuddSwapOutOfMem:
	(void) fprintf(table->err,"Error: naive_S_D_Swap out of memory\n");

	return (0);

} /* end of naive_S_D_Swap */


/**
	@brief Swaps two D-S adjacent variables.

*/
static int
naive_D_S_Swap(
	DdManager * table,
	int x,
	int y)
{
	DdNodePtr *xlist, *ylist;
	int xindex, yindex;
	int xslots, yslots;
	int xshift, yshift;
	int oldxkeys, oldykeys;
	int newxkeys, newykeys;
	int comple, newcomplement;
	int i;
	Cudd_VariableType varType;
	Cudd_LazyGroupType groupType;
	int posn;
	int isolated;
	DdNode *f,*f0,*f1,*f01,*f00,*f11,*f10,*newf1,*newf0;
	DdNode *g,*next;
	DdNodePtr *previousP;
	DdNode *tmp;
	DdNode *sentinel = &(table->sentinel);
	extern DD_OOMFP MMoutOfMemory;
	DD_OOMFP saveHandler;

#ifdef DD_DEBUG
	int count,idcheck;
#endif

#ifdef DD_DEBUG
	assert(x < y);
	assert(cuddNextHigh(table,x) == y);
	assert(table->subtables[x].keys != 0);
	assert(table->subtables[y].keys != 0);
	assert(table->subtables[x].dead == 0);
	assert(table->subtables[y].dead == 0);
#endif

	table->ddTotalNumberSwapping++;

	/* Get parameters of x subtable. */
	xindex = table->invperm[x];
	xlist = table->subtables[x].nodelist;
	oldxkeys = table->subtables[x].keys;
	xslots = table->subtables[x].slots;
	xshift = table->subtables[x].shift;

	/* Get parameters of y subtable. */
	yindex = table->invperm[y];
	ylist = table->subtables[y].nodelist;
	oldykeys = table->subtables[y].keys;
	yslots = table->subtables[y].slots;
	yshift = table->subtables[y].shift;

	newxkeys = 0;
	newykeys = oldykeys;

	isolated = - ((Cudd_Regular(table->vars[xindex])->ref == 1) +
	(Cudd_Regular(table->vars[yindex])->ref == 1));

	/* The nodes in the x layer that do not depend on
	** y will stay there; the others are put in a chain.
	** The chain is handled as a LIFO; g points to the beginning.
	*/
	g = NULL;
	if ((oldxkeys >= xslots || (unsigned) xslots == table->initSlots) &&
	oldxkeys <= DD_MAX_SUBTABLE_DENSITY * xslots) {
		for (i = 0; i < xslots; i++) {
			previousP = &(xlist[i]);
			f = *previousP;
			while (f != sentinel) {
				next = f->next;
				f1 = cuddT(f); f0 = cuddE(f);
				if (f1->index != (DdHalfWord) yindex &&
				Cudd_Regular(f0)->index != (DdHalfWord) yindex) {
					/* stays */
					newxkeys++;
					*previousP = f;
					previousP = &(f->next);
				} else {
					f->index = yindex;
					f->next = g;
					g = f;
				}
				f = next;
			} /* while there are elements in the collision chain */
			*previousP = sentinel;
		} /* for each slot of the x subtable */
	} else {		/* resize xlist */
		DdNode *h = NULL;
		DdNodePtr *newxlist;
		unsigned int newxslots;
		int newxshift;
		/* Empty current xlist. Nodes that stay go to list h;
		** nodes that move go to list g. */
		for (i = 0; i < xslots; i++) {
			f = xlist[i];
			while (f != sentinel) {
				next = f->next;
				f1 = cuddT(f); f0 = cuddE(f);
				if (f1->index != (DdHalfWord) yindex &&
				Cudd_Regular(f0)->index != (DdHalfWord) yindex) {
					/* stays */
					f->next = h;
					h = f;
					newxkeys++;
				} else {
					f->index = yindex;
					f->next = g;
					g = f;
				}
				f = next;
			} /* while there are elements in the collision chain */
		} /* for each slot of the x subtable */
		/* Decide size of new subtable. */
		newxshift = xshift;
		newxslots = xslots;
		while ((unsigned) oldxkeys > DD_MAX_SUBTABLE_DENSITY * newxslots) {
			newxshift--;
			newxslots <<= 1;
		}
		while ((unsigned) oldxkeys < newxslots &&
		newxslots > table->initSlots) {
			newxshift++;
			newxslots >>= 1;
		}
		/* Try to allocate new table. Be ready to back off. */
		saveHandler = MMoutOfMemory;
		MMoutOfMemory = table->outOfMemCallback;
		newxlist = ALLOC(DdNodePtr, newxslots);
		MMoutOfMemory = saveHandler;
		if (newxlist == NULL) {
			(void) fprintf(table->err, "Unable to resize subtable %d for lack of memory\n", i);
		} else {
			table->slots += ((int) newxslots - xslots);
			table->minDead = (unsigned)
			(table->gcFrac * (double) table->slots);
			table->cacheSlack = (int)
			ddMin(table->maxCacheHard, DD_MAX_CACHE_TO_SLOTS_RATIO
			* table->slots) - 2 * (int) table->cacheSlots;
			table->memused +=
			((int) newxslots - xslots) * sizeof(DdNodePtr);
			FREE(xlist);
			xslots =  newxslots;
			xshift = newxshift;
			xlist = newxlist;
		}
		/* Initialize new subtable. */
		for (i = 0; i < xslots; i++) {
			xlist[i] = sentinel;
		}
		/* Move nodes that were parked in list h to their new home. */
		f = h;
		while (f != NULL) {
			next = f->next;
			f1 = cuddT(f);
			f0 = cuddE(f);
			/* Check xlist for pair (f11,f01). */
			posn = ddHash(f1, f0, xshift);
			/* For each element tmp in collision list xlist[posn]. */
			previousP = &(xlist[posn]);
			tmp = *previousP;
			while (f1 < cuddT(tmp)) {
				previousP = &(tmp->next);
				tmp = *previousP;
			}
			while (f1 == cuddT(tmp) && f0 < cuddE(tmp)) {
				previousP = &(tmp->next);
				tmp = *previousP;
			}
			f->next = *previousP;
			*previousP = f;
			f = next;
		}
	}

#ifdef DD_COUNT
	table->swapSteps += oldxkeys - newxkeys;
#endif
	/* Take care of the x nodes that must be re-expressed.
	** They form a linked list pointed by g. Their index has been
	** already changed to yindex.
	*/
	f = g;
	while (f != NULL) {
		next = f->next;
		/* Find f1, f0, f11, f10, f01, f00. */
		f1 = cuddT(f);
#ifdef DD_DEBUG
		assert(!(Cudd_IsComplement(f1)));
#endif
		/* Before swap: f are decomposed by davio expansion,
		** while f1, f0 are decomposed by shannon expansions.
		** After swap: f are decomposed by shannon expansions,
		** while newf1, newf0 are decomposed by davio expansion.
		*/
		if ((int) f1->index == yindex) {
			f11 = cuddT(f1); f10 = cuddE(f1);
		} else {
			f11 = f10 = f1;
		}
#ifdef DD_DEBUG
		assert(!(Cudd_IsComplement(f11)));
#endif
		f0 = cuddE(f);
		comple = Cudd_IsComplement(f0);
		f0 = Cudd_Regular(f0);
		if ((int) f0->index == yindex) {
			f01 = cuddT(f0); f00 = cuddE(f0);
		} else {
			f01 = f00 = f0;
		}
		if (comple) {
			f01 = Cudd_Not(f01);
			f00 = Cudd_Not(f00);
		}
		/* Decrease ref count of f1. */
		cuddSatDec(f1->ref);
		/* Create the new T child. */
		if (f01 == Cudd_Not(DD_ONE(table))) {
			newf1 = f11;
			cuddSatInc(newf1->ref);
		} else {
			/* Check xlist for triple (xindex,f11,f01). */
			posn = ddHash(f11, f01, xshift);
			/* For each element newf1 in collision list xlist[posn]. */
			previousP = &(xlist[posn]);
			newf1 = *previousP;
			while (f11 < cuddT(newf1)) {
				previousP = &(newf1->next);
				newf1 = *previousP;
			}
			while (f11 == cuddT(newf1) && f01 < cuddE(newf1)) {
				previousP = &(newf1->next);
				newf1 = *previousP;
			}
			if (cuddT(newf1) == f11 && cuddE(newf1) == f01) {
				cuddSatInc(newf1->ref);
			} else { /* no match */
				newf1 = cuddDynamicAllocNode(table);
				if (newf1 == NULL) goto cuddSwapOutOfMem;
				newf1->index = xindex; newf1->ref = 1;
				cuddT(newf1) = f11;
				cuddE(newf1) = f01;
				/* Insert newf1 in the collision list xlist[posn];
				** increase the ref counts of f11 and f01.
				*/
				newxkeys++;
				newf1->next = *previousP;
				*previousP = newf1;
				cuddSatInc(f11->ref);
				tmp = Cudd_Regular(f01);
				cuddSatInc(tmp->ref);
			}
		}
		cuddT(f) = newf1;
#ifdef DD_DEBUG
		assert(!(Cudd_IsComplement(newf1)));
#endif

		/* Do the same for f0, keeping complement dots into account. */
		/* Decrease ref count of f0. */
		tmp = Cudd_Regular(f0);
		cuddSatDec(tmp->ref);
		/* Create the new E child. */
		if (f00 == Cudd_Not(DD_ONE(table))) {
			newf0 = f10;
			tmp = Cudd_Regular(newf0);
			cuddSatInc(tmp->ref);
		} else {
			/* make sure f10 is regular */
			newcomplement = Cudd_IsComplement(f10);
			if (newcomplement) {
				f10 = Cudd_Not(f10);
			}
			/* Check xlist for triple (xindex,f10,f00). */
			posn = ddHash(f10, f00, xshift);
			/* For each element newf0 in collision list xlist[posn]. */
			previousP = &(xlist[posn]);
			newf0 = *previousP;
			while (f10 < cuddT(newf0)) {
				previousP = &(newf0->next);
				newf0 = *previousP;
			}
			while (f10 == cuddT(newf0) && f00 < cuddE(newf0)) {
				previousP = &(newf0->next);
				newf0 = *previousP;
			}
			if (cuddT(newf0) == f10 && cuddE(newf0) == f00) {
				cuddSatInc(newf0->ref);
			} else { /* no match */
				newf0 = cuddDynamicAllocNode(table);
				if (newf0 == NULL) goto cuddSwapOutOfMem;
				newf0->index = xindex; newf0->ref = 1;
				cuddT(newf0) = f10;
				cuddE(newf0) = f00;
				/* Insert newf0 in the collision list xlist[posn];
				** increase the ref counts of f10 and f00.
				*/
				newxkeys++;
				newf0->next = *previousP;
				*previousP = newf0;
				cuddSatInc(f10->ref);
				tmp = Cudd_Regular(f00);
				cuddSatInc(tmp->ref);
			}
			if (newcomplement) {
				newf0 = Cudd_Not(newf0);
			}
		}
		cuddE(f) = newf0;

		/* Insert the modified f in ylist.
		** The modified f does not already exists in ylist.
		** (Because of the uniqueness of the cofactors.)
		*/
		posn = ddHash(newf1, newf0, yshift);
		newykeys++;
		previousP = &(ylist[posn]);
		tmp = *previousP;
		while (newf1 < cuddT(tmp)) {
			previousP = &(tmp->next);
			tmp = *previousP;
		}
		while (newf1 == cuddT(tmp) && newf0 < cuddE(tmp)) {
			previousP = &(tmp->next);
			tmp = *previousP;
		}
		f->next = *previousP;
		*previousP = f;
		f = next;
	} /* while f != NULL */

	/* GC the y layer. */

	/* For each node f in ylist. */
	for (i = 0; i < yslots; i++) {
		previousP = &(ylist[i]);
		f = *previousP;
		while (f != sentinel) {
			next = f->next;
			if (f->ref == 0) {
				tmp = cuddT(f);
				cuddSatDec(tmp->ref);
				tmp = Cudd_Regular(cuddE(f));
				cuddSatDec(tmp->ref);
				cuddDeallocNode(table,f);
				newykeys--;
			} else {
				*previousP = f;
				previousP = &(f->next);
			}
			f = next;
		} /* while f */
		*previousP = sentinel;
	} /* for i */

#ifdef DD_DEBUG
	count = 0;
	idcheck = 0;
	for (i = 0; i < yslots; i++) {
		f = ylist[i];
		while (f != sentinel) {
			count++;
			if (f->index != (DdHalfWord) yindex)
				idcheck++;
			f = f->next;
		}
	}
	if (count != newykeys) {
		(void) fprintf(table->out,
		"Error in finding newykeys\toldykeys = %d\tnewykeys = %d\tactual = %d\n",
		oldykeys,newykeys,count);
	}
	if (idcheck != 0)
		(void) fprintf(table->out,
		"Error in id's of ylist\twrong id's = %d\n",
		idcheck);
	count = 0;
	idcheck = 0;
	for (i = 0; i < xslots; i++) {
		f = xlist[i];
		while (f != sentinel) {
			count++;
			if (f->index != (DdHalfWord) xindex)
				idcheck++;
			f = f->next;
		}
	}
	if (count != newxkeys) {
		(void) fprintf(table->out,
		"Error in finding newxkeys\toldxkeys = %d \tnewxkeys = %d \tactual = %d\n",
		oldxkeys,newxkeys,count);
	}
	if (idcheck != 0)
		(void) fprintf(table->out,
		"Error in id's of xlist\twrong id's = %d\n",
		idcheck);
#endif
	isolated += (Cudd_Regular(table->vars[xindex])->ref == 1) +
	(Cudd_Regular(table->vars[yindex])->ref == 1);

	table->isolated += (unsigned int) isolated;

	/* Set the appropriate fields in table. */
	table->subtables[x].nodelist = ylist;
	table->subtables[x].slots = yslots;
	table->subtables[x].shift = yshift;
	table->subtables[x].keys = newykeys;
	table->subtables[x].maxKeys = yslots * DD_MAX_SUBTABLE_DENSITY;
	i = table->subtables[x].bindVar;
	table->subtables[x].bindVar = table->subtables[y].bindVar;
	table->subtables[y].bindVar = i;
	/* Adjust fields for lazy sifting. */
	varType = table->subtables[x].varType;
	table->subtables[x].varType = table->subtables[y].varType;
	table->subtables[y].varType = varType;
	i = table->subtables[x].pairIndex;
	table->subtables[x].pairIndex = table->subtables[y].pairIndex;
	table->subtables[y].pairIndex = i;
	i = table->subtables[x].varHandled;
	table->subtables[x].varHandled = table->subtables[y].varHandled;
	table->subtables[y].varHandled = i;
	groupType = table->subtables[x].varToBeGrouped;
	table->subtables[x].varToBeGrouped = table->subtables[y].varToBeGrouped;
	table->subtables[y].varToBeGrouped = groupType;

	table->subtables[y].nodelist = xlist;
	table->subtables[y].slots = xslots;
	table->subtables[y].shift = xshift;
	table->subtables[y].keys = newxkeys;
	table->subtables[y].maxKeys = xslots * DD_MAX_SUBTABLE_DENSITY;

	table->perm[xindex] = y; table->perm[yindex] = x;
	table->invperm[x] = yindex; table->invperm[y] = xindex;

	table->keys += newxkeys + newykeys - oldxkeys - oldykeys;

	return((int)(table->keys - table->isolated));

cuddSwapOutOfMem:
	(void) fprintf(table->err,"Error: naive_D_S_Swap out of memory\n");

	return (0);

} /* end of naive_D_S_Swap */


/**
	@brief Swaps two D-D adjacent variables.

*/
static int
naive_D_D_Swap(
  DdManager * table,
  int x,
  int y)
{
	DdNodePtr *xlist, *ylist;
	int xindex, yindex;
	int xslots, yslots;
	int xshift, yshift;
	int oldxkeys, oldykeys;
	int newxkeys, newykeys;
	int comple, newcomplement;
	int i;
	Cudd_VariableType varType;
	Cudd_LazyGroupType groupType;
	int posn;
	int isolated;
	DdNode *f,*f0,*f1,*f01,*f00,*f11,*f10,*newf1,*newf0;
	DdNode *g,*next;
	DdNodePtr *previousP;
	DdNode *tmp;
	DdNode *sentinel = &(table->sentinel);
	extern DD_OOMFP MMoutOfMemory;
	DD_OOMFP saveHandler;

#ifdef DD_DEBUG
	int    count,idcheck;
#endif

#ifdef DD_DEBUG
	assert(x < y);
	assert(cuddNextHigh(table,x) == y);
	assert(table->subtables[x].keys != 0);
	assert(table->subtables[y].keys != 0);
	assert(table->subtables[x].dead == 0);
	assert(table->subtables[y].dead == 0);
#endif

	table->ddTotalNumberSwapping++;

	/* Get parameters of x subtable. */
	xindex = table->invperm[x];
	xlist = table->subtables[x].nodelist;
	oldxkeys = table->subtables[x].keys;
	xslots = table->subtables[x].slots;
	xshift = table->subtables[x].shift;

	/* Get parameters of y subtable. */
	yindex = table->invperm[y];
	ylist = table->subtables[y].nodelist;
	oldykeys = table->subtables[y].keys;
	yslots = table->subtables[y].slots;
	yshift = table->subtables[y].shift;

	newxkeys = 0;
	newykeys = oldykeys;

	isolated = - ((Cudd_Regular(table->vars[xindex])->ref == 1) +
	(Cudd_Regular(table->vars[yindex])->ref == 1));

	/* The nodes in the x layer that do not depend on
	** y will stay there; the others are put in a chain.
	** The chain is handled as a LIFO; g points to the beginning.
	*/
	g = NULL;
	if ((oldxkeys >= xslots || (unsigned) xslots == table->initSlots) &&
	oldxkeys <= DD_MAX_SUBTABLE_DENSITY * xslots) {
		for (i = 0; i < xslots; i++) {
			previousP = &(xlist[i]);
			f = *previousP;
			while (f != sentinel) {
				next = f->next;
				f1 = cuddT(f); f0 = cuddE(f);
				if (f1->index != (DdHalfWord) yindex &&
				Cudd_Regular(f0)->index != (DdHalfWord) yindex) {
					/* stays */
					newxkeys++;
					*previousP = f;
					previousP = &(f->next);
				} else {
					f->index = yindex;
					f->next = g;
					g = f;
				}
				f = next;
			} /* while there are elements in the collision chain */
			*previousP = sentinel;
		} /* for each slot of the x subtable */
	} else {		/* resize xlist */
		DdNode *h = NULL;
		DdNodePtr *newxlist;
		unsigned int newxslots;
		int newxshift;
		/* Empty current xlist. Nodes that stay go to list h;
		** nodes that move go to list g. */
		for (i = 0; i < xslots; i++) {
			f = xlist[i];
			while (f != sentinel) {
				next = f->next;
				f1 = cuddT(f); f0 = cuddE(f);
				if (f1->index != (DdHalfWord) yindex &&
				Cudd_Regular(f0)->index != (DdHalfWord) yindex) {
					/* stays */
					f->next = h;
					h = f;
					newxkeys++;
				} else {
					f->index = yindex;
					f->next = g;
					g = f;
				}
				f = next;
			} /* while there are elements in the collision chain */
		} /* for each slot of the x subtable */
		/* Decide size of new subtable. */
		newxshift = xshift;
		newxslots = xslots;
		while ((unsigned) oldxkeys > DD_MAX_SUBTABLE_DENSITY * newxslots) {
			newxshift--;
			newxslots <<= 1;
		}
		while ((unsigned) oldxkeys < newxslots &&
		newxslots > table->initSlots) {
			newxshift++;
			newxslots >>= 1;
		}
		/* Try to allocate new table. Be ready to back off. */
		saveHandler = MMoutOfMemory;
		MMoutOfMemory = table->outOfMemCallback;
		newxlist = ALLOC(DdNodePtr, newxslots);
		MMoutOfMemory = saveHandler;
		if (newxlist == NULL) {
			(void) fprintf(table->err, "Unable to resize subtable %d for lack of memory\n", i);
		} else {
			table->slots += ((int) newxslots - xslots);
			table->minDead = (unsigned)
			(table->gcFrac * (double) table->slots);
			table->cacheSlack = (int)
			ddMin(table->maxCacheHard, DD_MAX_CACHE_TO_SLOTS_RATIO
			* table->slots) - 2 * (int) table->cacheSlots;
			table->memused +=
			((int) newxslots - xslots) * sizeof(DdNodePtr);
			FREE(xlist);
			xslots =  newxslots;
			xshift = newxshift;
			xlist = newxlist;
		}
		/* Initialize new subtable. */
		for (i = 0; i < xslots; i++) {
			xlist[i] = sentinel;
		}
		/* Move nodes that were parked in list h to their new home. */
		f = h;
		while (f != NULL) {
			next = f->next;
			f1 = cuddT(f);
			f0 = cuddE(f);
			/* Check xlist for pair (f11,f01). */
			posn = ddHash(f1, f0, xshift);
			/* For each element tmp in collision list xlist[posn]. */
			previousP = &(xlist[posn]);
			tmp = *previousP;
			while (f1 < cuddT(tmp)) {
				previousP = &(tmp->next);
				tmp = *previousP;
			}
			while (f1 == cuddT(tmp) && f0 < cuddE(tmp)) {
				previousP = &(tmp->next);
				tmp = *previousP;
			}
			f->next = *previousP;
			*previousP = f;
			f = next;
		}
	}

#ifdef DD_COUNT
	table->swapSteps += oldxkeys - newxkeys;
#endif
	/* Take care of the x nodes that must be re-expressed.
	** They form a linked list pointed by g. Their index has been
	** already changed to yindex.
	*/
	f = g;
	while (f != NULL) {
		next = f->next;
		/* Find f1, f0, f11, f10, f01, f00. */
		f1 = cuddT(f);
#ifdef DD_DEBUG
		assert(!(Cudd_IsComplement(f1)));
#endif
		/* Before swap: f are decomposed by davio expansion,
		** while f1, f0 are decomposed by davio expansions.
		** After swap: f are decomposed by davio expansions,
		** while newf1, newf0 are decomposed by davio expansion.
		*/
		if ((int) f1->index == yindex) {
			f11 = cuddT(f1); f10 = cuddE(f1);
		} else {
			f11 = f1;
			f10 = Cudd_Not(DD_ONE(table));
		}
#ifdef DD_DEBUG
		assert(!(Cudd_IsComplement(f11)));
#endif
		f0 = cuddE(f);
		comple = Cudd_IsComplement(f0);
		f0 = Cudd_Regular(f0);
		if ((int) f0->index == yindex) {
			f01 = cuddT(f0); f00 = cuddE(f0);
		} else {
			f01 = f0;
			f00 = Cudd_Not(DD_ONE(table));
		}
		if (comple) {
			f01 = Cudd_Not(f01);
		}
		/* Decrease ref count of f1. */
		cuddSatDec(f1->ref);
		/* Create the new T child. */
		if (f01 == Cudd_Not(DD_ONE(table))) {
			newf1 = f11;
			cuddSatInc(newf1->ref);
		} else {
			/* Check xlist for triple (xindex,f11,f01). */
			posn = ddHash(f11, f01, xshift);
			/* For each element newf1 in collision list xlist[posn]. */
			previousP = &(xlist[posn]);
			newf1 = *previousP;
			while (f11 < cuddT(newf1)) {
				previousP = &(newf1->next);
				newf1 = *previousP;
			}
			while (f11 == cuddT(newf1) && f01 < cuddE(newf1)) {
				previousP = &(newf1->next);
				newf1 = *previousP;
			}
			if (cuddT(newf1) == f11 && cuddE(newf1) == f01) {
				cuddSatInc(newf1->ref);
			} else { /* no match */
				newf1 = cuddDynamicAllocNode(table);
				if (newf1 == NULL) goto cuddSwapOutOfMem;
				newf1->index = xindex; newf1->ref = 1;
				cuddT(newf1) = f11;
				cuddE(newf1) = f01;
				/* Insert newf1 in the collision list xlist[posn];
				** increase the ref counts of f11 and f01.
				*/
				newxkeys++;
				newf1->next = *previousP;
				*previousP = newf1;
				cuddSatInc(f11->ref);
				tmp = Cudd_Regular(f01);
				cuddSatInc(tmp->ref);
			}
		}
		cuddT(f) = newf1;
#ifdef DD_DEBUG
		assert(!(Cudd_IsComplement(newf1)));
#endif

		/* Do the same for f0, keeping complement dots into account. */
		/* Decrease ref count of f0. */
		tmp = Cudd_Regular(f0);
		cuddSatDec(tmp->ref);
		/* Create the new E child. */
		if (f00 == Cudd_Not(DD_ONE(table))) {
			newf0 = f10;
			tmp = Cudd_Regular(newf0);
			cuddSatInc(tmp->ref);
		} else {
			/* make sure f10 is regular */
			newcomplement = Cudd_IsComplement(f10);
			if (newcomplement) {
				f10 = Cudd_Not(f10);
			}
			/* Check xlist for triple (xindex,f10,f00). */
			posn = ddHash(f10, f00, xshift);
			/* For each element newf0 in collision list xlist[posn]. */
			previousP = &(xlist[posn]);
			newf0 = *previousP;
			while (f10 < cuddT(newf0)) {
				previousP = &(newf0->next);
				newf0 = *previousP;
			}
			while (f10 == cuddT(newf0) && f00 < cuddE(newf0)) {
				previousP = &(newf0->next);
				newf0 = *previousP;
			}
			if (cuddT(newf0) == f10 && cuddE(newf0) == f00) {
				cuddSatInc(newf0->ref);
			} else { /* no match */
				newf0 = cuddDynamicAllocNode(table);
				if (newf0 == NULL) goto cuddSwapOutOfMem;
				newf0->index = xindex; newf0->ref = 1;
				cuddT(newf0) = f10;
				cuddE(newf0) = f00;
				/* Insert newf0 in the collision list xlist[posn];
				** increase the ref counts of f10 and f00.
				*/
				newxkeys++;
				newf0->next = *previousP;
				*previousP = newf0;
				cuddSatInc(f10->ref);
				tmp = Cudd_Regular(f00);
				cuddSatInc(tmp->ref);
			}
			if (newcomplement) {
				newf0 = Cudd_Not(newf0);
			}
		}
		cuddE(f) = newf0;

		/* Insert the modified f in ylist.
		** The modified f does not already exists in ylist.
		** (Because of the uniqueness of the cofactors.)
		*/
		posn = ddHash(newf1, newf0, yshift);
		newykeys++;
		previousP = &(ylist[posn]);
		tmp = *previousP;
		while (newf1 < cuddT(tmp)) {
			previousP = &(tmp->next);
			tmp = *previousP;
		}
		while (newf1 == cuddT(tmp) && newf0 < cuddE(tmp)) {
			previousP = &(tmp->next);
			tmp = *previousP;
		}
		f->next = *previousP;
		*previousP = f;
		f = next;
	} /* while f != NULL */

	/* GC the y layer. */

	/* For each node f in ylist. */
	for (i = 0; i < yslots; i++) {
		previousP = &(ylist[i]);
		f = *previousP;
		while (f != sentinel) {
			next = f->next;
			if (f->ref == 0) {
				tmp = cuddT(f);
				cuddSatDec(tmp->ref);
				tmp = Cudd_Regular(cuddE(f));
				cuddSatDec(tmp->ref);
				cuddDeallocNode(table,f);
				newykeys--;
			} else {
				*previousP = f;
				previousP = &(f->next);
			}
			f = next;
		} /* while f */
		*previousP = sentinel;
	} /* for i */

#ifdef DD_DEBUG
	count = 0;
	idcheck = 0;
	for (i = 0; i < yslots; i++) {
		f = ylist[i];
		while (f != sentinel) {
			count++;
			if (f->index != (DdHalfWord) yindex)
				idcheck++;
			f = f->next;
		}
	}
	if (count != newykeys) {
		(void) fprintf(table->out,
		"Error in finding newykeys\toldykeys = %d\tnewykeys = %d\tactual = %d\n",
		oldykeys,newykeys,count);
	}
	if (idcheck != 0)
		(void) fprintf(table->out,
		"Error in id's of ylist\twrong id's = %d\n",
		idcheck);
	count = 0;
	idcheck = 0;
	for (i = 0; i < xslots; i++) {
		f = xlist[i];
		while (f != sentinel) {
			count++;
			if (f->index != (DdHalfWord) xindex)
				idcheck++;
			f = f->next;
		}
	}
	if (count != newxkeys) {
		(void) fprintf(table->out,
		"Error in finding newxkeys\toldxkeys = %d \tnewxkeys = %d \tactual = %d\n",
		oldxkeys,newxkeys,count);
	}
	if (idcheck != 0)
		(void) fprintf(table->out,
		"Error in id's of xlist\twrong id's = %d\n",
		idcheck);
#endif
	isolated += (Cudd_Regular(table->vars[xindex])->ref == 1) +
	(Cudd_Regular(table->vars[yindex])->ref == 1);

	table->isolated += (unsigned int) isolated;

	/* Set the appropriate fields in table. */
	table->subtables[x].nodelist = ylist;
	table->subtables[x].slots = yslots;
	table->subtables[x].shift = yshift;
	table->subtables[x].keys = newykeys;
	table->subtables[x].maxKeys = yslots * DD_MAX_SUBTABLE_DENSITY;
	i = table->subtables[x].bindVar;
	table->subtables[x].bindVar = table->subtables[y].bindVar;
	table->subtables[y].bindVar = i;
	/* Adjust fields for lazy sifting. */
	varType = table->subtables[x].varType;
	table->subtables[x].varType = table->subtables[y].varType;
	table->subtables[y].varType = varType;
	i = table->subtables[x].pairIndex;
	table->subtables[x].pairIndex = table->subtables[y].pairIndex;
	table->subtables[y].pairIndex = i;
	i = table->subtables[x].varHandled;
	table->subtables[x].varHandled = table->subtables[y].varHandled;
	table->subtables[y].varHandled = i;
	groupType = table->subtables[x].varToBeGrouped;
	table->subtables[x].varToBeGrouped = table->subtables[y].varToBeGrouped;
	table->subtables[y].varToBeGrouped = groupType;

	table->subtables[y].nodelist = xlist;
	table->subtables[y].slots = xslots;
	table->subtables[y].shift = xshift;
	table->subtables[y].keys = newxkeys;
	table->subtables[y].maxKeys = xslots * DD_MAX_SUBTABLE_DENSITY;

	table->perm[xindex] = y; table->perm[yindex] = x;
	table->invperm[x] = yindex; table->invperm[y] = xindex;
	
	table->keys += newxkeys + newykeys - oldxkeys - oldykeys;

	return((int)(table->keys - table->isolated));

cuddSwapOutOfMem:
	(void) fprintf(table->err,"Error: naive_D_D_Swap out of memory\n");

	return (0);

} /* end of naive_D_D_Swap */

#if 0
/**
  @brief Linearly combines two adjacent variables, a naive version,
	no interaction matrix.

  @details Specifically, replaces the top variable with the exclusive
  nor of the two variables.  It assumes that no dead nodes are present
  on entry to this procedure.  The procedure then guarantees that no
  dead nodes will be present when it terminates.  naiveLinearInPlace
  assumes that x &lt; y.

  @return the number of keys in the table if successful; 0 otherwise.

  @sideeffect The two subtables corrresponding to variables x and y are
  modified. The global counters of the unique table are also affected.

  @see cuddSwapInPlace

*/
int
naiveLinearInPlace(
  DdManager * table,
  int  x,
  int  y)
{
	DdNodePtr *xlist, *ylist;
	int    xindex, yindex;
	int    xslots, yslots;
	int    xshift, yshift;
#if defined(DD_COUNT) || defined(DD_DEBUG)
	int    oldxkeys;
#endif
	int oldykeys;
	int    newxkeys, newykeys;
	int    comple, newcomplement;
	int    i;
	int    posn;
	int    isolated;
	DdNode *f,*f0,*f1,*f01,*f00,*f11,*f10,*newf1,*newf0;
	DdNode *g,*next,*last=NULL;
	DdNodePtr *previousP;
	DdNode *tmp;
	DdNode *sentinel = &(table->sentinel);
#ifdef DD_DEBUG
	int    count, idcheck;
#endif

#ifdef DD_DEBUG
	assert(x < y);
	assert(cuddNextHigh(table,x) == y);
	assert(table->subtables[x].keys != 0);
	assert(table->subtables[y].keys != 0);
	assert(table->subtables[x].dead == 0);
	assert(table->subtables[y].dead == 0);
#endif

	xindex = table->invperm[x];
	yindex = table->invperm[y];

#ifdef DD_STATS
	table->totalNumberLinearTr++;
#endif
	/* Get parameters of x subtable. */
	xlist = table->subtables[x].nodelist;
#if defined(DD_COUNT) || defined(DD_DEBUG)
	oldxkeys = table->subtables[x].keys;
#endif
	xslots = table->subtables[x].slots;
	xshift = table->subtables[x].shift;

	/* Get parameters of y subtable. */
	ylist = table->subtables[y].nodelist;
	oldykeys = table->subtables[y].keys;
	yslots = table->subtables[y].slots;
	yshift = table->subtables[y].shift;

	newxkeys = 0;
	newykeys = oldykeys;

	/* Check whether the two projection functions involved in this
	** swap are isolated. At the end, we'll be able to tell how many
	** isolated projection functions are there by checking only these
	** two functions again. This is done to eliminate the isolated
	** projection functions from the node count.
	*/
	isolated = - ((table->vars[xindex]->ref == 1) +
	(table->vars[yindex]->ref == 1));

	/* The nodes in the x layer are put in a chain.
	** The chain is handled as a FIFO; g points to the beginning and
	** last points to the end.
	*/
	g = NULL;
#ifdef DD_DEBUG
	last = NULL;
#endif
	for (i = 0; i < xslots; i++) {
		f = xlist[i];
		if (f == sentinel) continue;
		xlist[i] = sentinel;
		if (g == NULL) {
			g = f;
		} else {
			last->next = f;
		}
		while ((next = f->next) != sentinel) {
			f = next;
		} /* while there are elements in the collision chain */
		last = f;
	} /* for each slot of the x subtable */
#ifdef DD_DEBUG
	/* last is always assigned in the for loop because there is at
	** least one key */
	assert(last != NULL);
#endif
	last->next = NULL;

#ifdef DD_COUNT
	table->swapSteps += oldxkeys;
#endif
	/* Take care of the x nodes that must be re-expressed.
	** They form a linked list pointed by g.
	*/
	f = g;
	while (f != NULL) {
		next = f->next;
		/* Find f1, f0, f11, f10, f01, f00. */
		f1 = cuddT(f);
#ifdef DD_DEBUG	
		assert(!(Cudd_IsComplement(f1)));
#endif
		if ((int) f1->index == yindex) {
			f11 = cuddT(f1); f10 = cuddE(f1);
		} else {
			f11 = f10 = f1;
		}
#ifdef DD_DEBUG	
		assert(!(Cudd_IsComplement(f11)));
#endif
		f0 = cuddE(f);
		comple = Cudd_IsComplement(f0);
		f0 = Cudd_Regular(f0);
		if ((int) f0->index == yindex) {
			f01 = cuddT(f0); f00 = cuddE(f0);
		} else {
			f01 = f00 = f0;
		}
		if (comple) {
			f01 = Cudd_Not(f01);
			f00 = Cudd_Not(f00);
		}
		/* Decrease ref count of f1. */
		cuddSatDec(f1->ref);
		/* Create the new T child. */
		if (f11 == f00) {
			newf1 = f11;
			cuddSatInc(newf1->ref);
		} else {
			/* Check ylist for triple (yindex,f11,f00). */
			posn = ddHash(f11, f00, yshift);
			/* For each element newf1 in collision list ylist[posn]. */
			previousP = &(ylist[posn]);
			newf1 = *previousP;
			while (f11 < cuddT(newf1)) {
				previousP = &(newf1->next);
				newf1 = *previousP;
			}
			while (f11 == cuddT(newf1) && f00 < cuddE(newf1)) {
				previousP = &(newf1->next);
				newf1 = *previousP;
			}
			if (cuddT(newf1) == f11 && cuddE(newf1) == f00) {
				cuddSatInc(newf1->ref);
			} else { /* no match */
				newf1 = cuddDynamicAllocNode(table);
				if (newf1 == NULL)
				goto cuddLinearOutOfMem;
				newf1->index = yindex; newf1->ref = 1;
				cuddT(newf1) = f11;
				cuddE(newf1) = f00;
				/* Insert newf1 in the collision list ylist[posn];
				** increase the ref counts of f11 and f00.
				*/
				newykeys++;
				newf1->next = *previousP;
				*previousP = newf1;
				cuddSatInc(f11->ref);
				tmp = Cudd_Regular(f00);
				cuddSatInc(tmp->ref);
			}
		}
		cuddT(f) = newf1;
#ifdef DD_DEBUG	
		assert(!(Cudd_IsComplement(newf1)));
#endif

		/* Do the same for f0, keeping complement dots into account. */
		/* decrease ref count of f0 */
		tmp = Cudd_Regular(f0);
		cuddSatDec(tmp->ref);
		/* create the new E child */
		if (f01 == f10) {
			newf0 = f01;
			tmp = Cudd_Regular(newf0);
			cuddSatInc(tmp->ref);
		} else {
			/* make sure f01 is regular */
			newcomplement = Cudd_IsComplement(f01);
			if (newcomplement) {
				f01 = Cudd_Not(f01);
				f10 = Cudd_Not(f10);
			}
			/* Check ylist for triple (yindex,f01,f10). */
			posn = ddHash(f01, f10, yshift);
			/* For each element newf0 in collision list ylist[posn]. */
			previousP = &(ylist[posn]);
			newf0 = *previousP;
			while (f01 < cuddT(newf0)) {
				previousP = &(newf0->next);
				newf0 = *previousP;
			}
			while (f01 == cuddT(newf0) && f10 < cuddE(newf0)) {
				previousP = &(newf0->next);
				newf0 = *previousP;
			}
			if (cuddT(newf0) == f01 && cuddE(newf0) == f10) {
				cuddSatInc(newf0->ref);
			} else { /* no match */
				newf0 = cuddDynamicAllocNode(table);
				if (newf0 == NULL)
					goto cuddLinearOutOfMem;
				newf0->index = yindex; newf0->ref = 1;
				cuddT(newf0) = f01;
				cuddE(newf0) = f10;
				/* Insert newf0 in the collision list ylist[posn];
				** increase the ref counts of f01 and f10.
				*/
				newykeys++;
				newf0->next = *previousP;
				*previousP = newf0;
				cuddSatInc(f01->ref);
				tmp = Cudd_Regular(f10);
				cuddSatInc(tmp->ref);
			}
			if (newcomplement) {
				newf0 = Cudd_Not(newf0);
			}
		}
		cuddE(f) = newf0;

		/* Re-insert the modified f in xlist.
		** The modified f does not already exists in xlist.
		** (Because of the uniqueness of the cofactors.)
		*/
		posn = ddHash(newf1, newf0, xshift);
		newxkeys++;
		previousP = &(xlist[posn]);
		tmp = *previousP;
		while (newf1 < cuddT(tmp)) {
			previousP = &(tmp->next);
			tmp = *previousP;
		}
		while (newf1 == cuddT(tmp) && newf0 < cuddE(tmp)) {
			previousP = &(tmp->next);
			tmp = *previousP;
		}
		f->next = *previousP;
		*previousP = f;
		f = next;
	} /* while f != NULL */

	/* GC the y layer. */

	/* For each node f in ylist. */
	for (i = 0; i < yslots; i++) {
		previousP = &(ylist[i]);
		f = *previousP;
		while (f != sentinel) {
			next = f->next;
			if (f->ref == 0) {
				tmp = cuddT(f);
				cuddSatDec(tmp->ref);
				tmp = Cudd_Regular(cuddE(f));
				cuddSatDec(tmp->ref);
				cuddDeallocNode(table,f);
				newykeys--;
			} else {
				*previousP = f;
				previousP = &(f->next);
			}
			f = next;
		} /* while f */
		*previousP = sentinel;
	} /* for every collision list */

#ifdef DD_DEBUG
#if 0
	(void) fprintf(table->out,"Linearly combining %d and %d\n",x,y);
#endif
	count = 0;
	idcheck = 0;
	for (i = 0; i < yslots; i++) {
		f = ylist[i];
		while (f != sentinel) {
			count++;
			if (f->index != (DdHalfWord) yindex)
				idcheck++;
			f = f->next;
		}
	}
	if (count != newykeys) {
		fprintf(table->err,"Error in finding newykeys\toldykeys = %d\tnewykeys = %d\tactual = %d\n",oldykeys,newykeys,count);
	}
	if (idcheck != 0)
		fprintf(table->err,"Error in id's of ylist\twrong id's = %d\n",idcheck);
	count = 0;
	idcheck = 0;
	for (i = 0; i < xslots; i++) {
		f = xlist[i];
		while (f != sentinel) {
			count++;
			if (f->index != (DdHalfWord) xindex)
				idcheck++;
			f = f->next;
		}
	}
	if (count != newxkeys || newxkeys != oldxkeys) {
		fprintf(table->err,"Error in finding newxkeys\toldxkeys = %d \tnewxkeys = %d \tactual = %d\n",oldxkeys,newxkeys,count);
	}
	if (idcheck != 0)
		fprintf(table->err,"Error in id's of xlist\twrong id's = %d\n",idcheck);
#endif

	isolated += (table->vars[xindex]->ref == 1) +
	(table->vars[yindex]->ref == 1);
	table->isolated += (unsigned int) isolated;

	/* Set the appropriate fields in table. */
	table->subtables[y].keys = newykeys;

	/* Here we should update the linear combination table
	** to record that x <- x EXNOR y. This is done by complementing
	** the (x,y) entry of the table.
	*/

	table->keys += newykeys - oldykeys;

#ifdef DD_DEBUG
	if (table->enableExtraDebug) {
		(void) Cudd_DebugCheck(table);
	}
#endif

	return((int)(table->keys - table->isolated));

cuddLinearOutOfMem:
	(void) fprintf(table->err,"Error: naiveLinearInPlace out of memory\n");

	return (0);

} /* end of naiveLinearInPlace */
#endif
