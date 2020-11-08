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
#include "mtrInt.h"
#include "cuddInt.h"
#include "bkfddInt.h"

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
static int oetSiftingAux (DdManager *table, int x, int xLow, int xHigh);
static Move * oetSiftingUp (DdManager *table, int y, int xLow, Move *best);
static Move * oetSiftingDown (DdManager *table, int x, int xHigh, Move *best);
static int oetSiftingBackward (DdManager *table, int currentPos, Move *best);
static int complexSwap (DdManager * table, int x, int y);
static int ddUniqueCompare (void const *ptrX, void const *ptrY);
static int chooseSND4inPlace(DdManager * table,	int level);

/** \endcond */

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**
  @brief Implementation of BKFDD's OET-sifting algorithm. ORIGINAL VERSION of OET

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
oetSifting(
	DdManager * table,
	int lower,
	int upper)
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
		goto oetSiftingFailed;
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
		result = oetSiftingAux(table, x, lower, upper);
		if (!result) goto oetSiftingFailed;
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

oetSiftingFailed:

	if (var != NULL) FREE(var);

	return(0);

} /* end of oetSifting */

/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/


/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/

/**
  @brief In BKFDD's oet-sifting, Given xLow <= x <= xHigh moves x 
  up and down between the boundaries.
  If reach the bottom level, change expansion types.

  @details Finds the best position and does the required changes.

  @return 1 if successful; 0 otherwise.

  @sideeffect None

*/
static int
oetSiftingAux(
  DdManager * table,
  int  x,
  int  xLow,
  int  xHigh)
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
	if (bestPos == NULL) goto oetSiftingAuxOutOfMem;
	/* Store initial information */
	bestPos->x = bestPos->y = x;
	bestPos->flags = table->expansion[x];
	bestPos->size = (int) (table->keys - table->isolated);;
	bestPos->next = NULL;

	if (x == xLow) {
		moveDown = oetSiftingDown(table,x,xHigh,bestPos);
		/* At this point x --> xHigh unless bounding occurred. */
		if (moveDown == (Move *) CUDD_OUT_OF_MEM) goto oetSiftingAuxOutOfMem;
		/* Move backward(up) and stop at best position. */
		result = oetSiftingBackward(table,table->perm[xindex],bestPos);
		if (!result) goto oetSiftingAuxOutOfMem;
	} else if (x == xHigh) {
		moveUp = oetSiftingUp(table,x,xLow,bestPos);
		/* At this point x --> xLow unless bounding occurred. */
		if (moveUp == (Move *) CUDD_OUT_OF_MEM) goto oetSiftingAuxOutOfMem;
		/* Move backward(down) and stop at best position. */
		result = oetSiftingBackward(table,table->perm[xindex],bestPos);
		if (!result) goto oetSiftingAuxOutOfMem;
	} else if ((x - xLow) > (xHigh - x)) { /* must go down first: shorter */
		moveDown = oetSiftingDown(table,x,xHigh,bestPos);
		/* At this point x --> xHigh unless bounding occurred. */
		if (moveDown == (Move *) CUDD_OUT_OF_MEM) goto oetSiftingAuxOutOfMem;
		if (moveDown != NULL) {
			x = moveDown->y;
		}
		moveUp = oetSiftingUp(table,x,xLow,bestPos);
		if (moveUp == (Move *) CUDD_OUT_OF_MEM) goto oetSiftingAuxOutOfMem;
		/* Move backward(down) and stop at best position */
		result = oetSiftingBackward(table,table->perm[xindex],bestPos);
		if (!result) goto oetSiftingAuxOutOfMem;
	} else {
		moveUp = oetSiftingUp(table,x,xLow,bestPos);
		/* At this point x --> xLow unless bounding occurred. */
		if (moveUp == (Move *) CUDD_OUT_OF_MEM) goto oetSiftingAuxOutOfMem;
		if (moveUp != NULL) {
			x = moveUp->x;
		}
		moveDown = oetSiftingDown(table,x,xHigh,bestPos);
		if (moveDown == (Move *) CUDD_OUT_OF_MEM) goto oetSiftingAuxOutOfMem;
		/* Move backward(up) and stop at best position. */
		result = oetSiftingBackward(table,table->perm[xindex],bestPos);
		if (!result) goto oetSiftingAuxOutOfMem;
	}
	
	if (isBi(table->expansion[table->size-1])) {
		if (!changeExpnBetweenBiCla(table, table->size-1)) {
			printf("oetSiftingAux: bottom Cla-expn failed\n");
			goto oetSiftingAuxOutOfMem;
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

oetSiftingAuxOutOfMem:
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

} /* end of oetSiftingAux */


/**
  @brief Sifts a variable up.

  @details Moves y up until either it reaches the bound (xLow) or the
  size of the %DD heap increases too much. BKFDD's oet-sifting 
  is similar to Rudell's sifting.

  @return the set of moves in case of success; NULL if memory is full.

  @sideeffect None

*/
static Move *
oetSiftingUp(
  DdManager * table,
  int y,
  int xLow,
	Move *best)
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
		size = complexSwap(table,x,y);
		if (size == 0) goto oetSiftingUpOutOfMem;
		// change expansion
		if (!chooseSND4inPlace(table,x)) {
			goto oetSiftingUpOutOfMem;
		}
		size = (int) (table->keys - table->isolated);
		move = (Move *) cuddDynamicAllocNode(table);
		if (move == NULL) goto oetSiftingUpOutOfMem;
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

oetSiftingUpOutOfMem:
	while (moves != NULL) {
		move = moves->next;
		cuddDeallocMove(table, moves);
		moves = move;
	}

	return((Move *) CUDD_OUT_OF_MEM);

} /* end of oetSiftingUp */


/**
  @brief Sifts a variable down.

  @details Moves x down until either it reaches the bound (xHigh) or
  the size of the %DD heap increases too much. In BKFDD's oet-sifting,
  if reach the bottom level, change expansion types.

  @return the set of moves in case of success; NULL if memory is full.

  @sideeffect None

*/
static Move *
oetSiftingDown(
  DdManager * table,
  int x,
  int xHigh,
	Move *best)
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
		size = complexSwap(table,x,y);
		if (size == 0) goto oetSiftingDownOutOfMem;
		// change expansion
		if (!chooseSND4inPlace(table,y)) {
			goto oetSiftingDownOutOfMem;
		}
		size = (int) (table->keys - table->isolated);
		move = (Move *) cuddDynamicAllocNode(table);
		if (move == NULL) goto oetSiftingDownOutOfMem;
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

oetSiftingDownOutOfMem:
	while (moves != NULL) {
		move = moves->next;
		cuddDeallocMove(table, moves);
		moves = move;
	}

	return((Move *) CUDD_OUT_OF_MEM);

} /* end of oetSiftingDown */


/**
  @brief Given a set of moves, returns the %DD heap to the position
  giving the minimum size.

  @details In case of ties, returns to the closest position giving the
  minimum size.

  @return 1 in case of success; 0 otherwise.

  @sideeffect None

*/
static int
oetSiftingBackward(
	DdManager * table,
	int  currentPos,
	Move * best)
{
	int res, pos, expn;
	pos = best->x;
	expn = (int)best->flags;

	while (currentPos < pos) { // move down to best position
		res = complexSwap(table,currentPos,currentPos+1);
		if (res == 0) {
			printf("oetSiftingBackward: down to best failed\n");
			return(0);
		}
		currentPos ++;
	}
	while (currentPos > pos) { // move up to best position
		res = complexSwap(table,currentPos-1,currentPos);
		if (res == 0) {
			printf("oetSiftingBackward: up to best failed\n");
			return(0);
		}
		currentPos --;
	}
	assert(currentPos == pos);
	// change to best expn
	if (table->expansion[pos] != expn) {
		if ( (isBi(table->expansion[pos]) && isCla(expn)) ||
					(isCla(table->expansion[pos]) && isBi(expn)) ) {
			if (!changeExpnBetweenBiCla(table, pos)) {
				printf("oetSiftingBackward: roll back failed\n");
				return(0);
			}
		}
		if (table->expansion[pos] != expn) {
			if (!changeExpnBetweenSND(table, pos)) {
				printf("oetSiftingBackward: roll back failed\n");
				return(0);
			}
		}
	}
	assert((int)(table->keys-table->isolated) == best->size);

	return(1);

} /* end of oetSiftingBackward */


/**
  @brief Swaps two adjacent variables.
	 	1. Make sure two adjacent variables associated with cla-expn.
		2. Naive Swap two adjacent.
		3. Recover two adjacent to original expansions.
*/
static int
complexSwap(
  DdManager * table,
  int  x,
  int  y)
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
		if (!changeExpnBetweenBiCla(table, y)) {
			printf("complexSwap: change expn failed\n");
			goto swapFailed;
		}
	}

	if (isBi(table->expansion[x])) {
		xBi = 1;
		if (!changeExpnBetweenBiCla(table, x)) {
			printf("complexSwap: change expn failed\n");
			goto swapFailed;
		}
	}

	if ( (x > 0) && isBi(table->expansion[x-1])) {
		x_1Bi = 1;
		if (!changeExpnBetweenBiCla(table, x-1)) {
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
		if (!changeExpnBetweenBiCla(table, x-1)) {
			printf("complexSwap: change expn failed\n");
			goto swapFailed;
		}
	}
	if (yBi) {
		if (!changeExpnBetweenBiCla(table, x)) {
			printf("complexSwap: change expn failed\n");
			goto swapFailed;
		}
	}
	if (xBi) {
		if (!changeExpnBetweenBiCla(table, y)) {
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
} /* end of complexSwap */


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
	@brief choose better expansion from {CS, BS, CND, BND}
*/
static int
chooseSND4inPlace(
	DdManager * table,
	int level)
{
	unsigned int oldKeysTotal, newKeysTotal;
	unsigned int newKeysTotal1, newKeysTotal2, newKeysTotal3;
	int ii, initExpn, expn1, expn2, expn3, expn;

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

	if ( (nonShan == upper_bound) &&
			isShan(table->expansion[level]) ) {
		/* If number of nonShan expansion reach upper bound
		and current level associated with Shan, then try BS or CS. */
		if (!changeExpnBetweenBiCla(table,level)) {
			printf("chooseSND4inPlace: %d, choose better expn failed\n", level);
			goto chooseFailed;
		}
		newKeysTotal = table->keys-table->isolated;
		double key = newKeysTotal;
		double keyNew = oldKeysTotal * table->choose_new_bound_factor;
		if ( key >= keyNew ) {
			if (!changeExpnBetweenBiCla(table,level)) {
				printf("chooseSND4inPlace: %d, roll back failed\n", level);
				goto chooseFailed;
			}
			newKeysTotal = table->keys-table->isolated;
			assert(newKeysTotal == oldKeysTotal);
		}
	} else {
		/*
			1. nonShan == upper_bound and !isShan
			2. nonShan < upper_bound	and isShan
			3. nonShan < upper_bound  and !isShan
		*/
		initExpn = table->expansion[level];
		if ((table->expansion[level] == CS) || (table->expansion[level] == BND)) {
			// CS->CND->BND->BS or BND->BS->CS->CND
			// CS->CND or BND->BS
			if (!changeExpnBetweenSND(table,level)) {
				printf("chooseSND4inPlace: %d, choose better expn failed\n", level);
				goto chooseFailed;
			}
			newKeysTotal1 = table->keys-table->isolated;
			expn1 = table->expansion[level];
			// CND->BND or BS->CS
			if (!changeExpnBetweenBiCla(table,level)) {
				printf("chooseSND4inPlace: %d, choose better expn failed\n", level);
				goto chooseFailed;
			}
			newKeysTotal2 = table->keys-table->isolated;
			expn2 = table->expansion[level];
			// BND->BS or CS->CND
			if (!changeExpnBetweenSND(table,level)) {
				printf("chooseSND4inPlace: %d, choose better expn failed\n", level);
				goto chooseFailed;
			}
			newKeysTotal3 = table->keys-table->isolated;
			expn3 = table->expansion[level];
			newKeysTotal = ddMin(newKeysTotal1, newKeysTotal2);
			newKeysTotal = ddMin(newKeysTotal, newKeysTotal3);
			assert((table->expansion[level] == BS) || (table->expansion[level] == CND));
			if (newKeysTotal == newKeysTotal1) {
				expn = expn1;
			} else if (newKeysTotal == newKeysTotal2) {
				expn = expn2;
			} else {
				expn = expn3;
			}
			double key = newKeysTotal;
			double keyNew = oldKeysTotal * table->choose_new_bound_factor;
			double keyDav = oldKeysTotal * table->choose_dav_bound_factor;
			if ( (key >= keyNew) ||
					(!isShan(expn) && (key >= keyDav)) ) {
				// roll back to initial expansion, BS->CS or CND->BND
				if (!changeExpnBetweenBiCla(table,level)) {
					printf("chooseSND4inPlace: %d, roll back failed\n", level);
					goto chooseFailed;
				}
				assert((table->keys-table->isolated) == oldKeysTotal);
			} else { // CND<-BND<-BS or BS<-CS<-CND
				if (newKeysTotal == newKeysTotal1) {
					if (!changeExpnBetweenSND(table,level)) {
						printf("chooseSND4inPlace: %d, roll back failed\n", level);
						goto chooseFailed;
					}
					assert((table->keys-table->isolated) == newKeysTotal2);
					if (!changeExpnBetweenBiCla(table,level)) {
						printf("chooseSND4inPlace: %d, roll back failed\n", level);
						goto chooseFailed;
					}
					assert((table->keys-table->isolated) == newKeysTotal1);
				} else if (newKeysTotal == newKeysTotal2) {
					if (!changeExpnBetweenSND(table,level)) {
						printf("chooseSND4inPlace: %d, roll back failed\n", level);
						goto chooseFailed;
					}
					assert((table->keys-table->isolated) == newKeysTotal2);
				}
			}
		} else if ((table->expansion[level] == CND) || (table->expansion[level] == BS)) {
			// CND->BND->BS->CS or BS->CS->CND->BND
			// CND->BND or BS->CS
			if (!changeExpnBetweenBiCla(table,level)) {
				printf("chooseSND4inPlace: %d, choose better expn failed\n", level);
				goto chooseFailed;
			}
			newKeysTotal1 = table->keys-table->isolated;
			expn1 = table->expansion[level];
			// BND->BS or CS->CND
			if (!changeExpnBetweenSND(table,level)) {
				printf("chooseSND4inPlace: %d, choose better expn failed\n", level);
				goto chooseFailed;
			}
			newKeysTotal2 = table->keys-table->isolated;
			expn2 = table->expansion[level];
			// BS->CS or CND->BND
			if (!changeExpnBetweenBiCla(table,level)) {
				printf("chooseSND4inPlace: %d, choose better expn failed\n", level);
				goto chooseFailed;
			}
			newKeysTotal3 = table->keys-table->isolated;
			expn3 = table->expansion[level];
			newKeysTotal = ddMin(newKeysTotal1, newKeysTotal2);
			newKeysTotal = ddMin(newKeysTotal, newKeysTotal3);
			assert((table->expansion[level] == CS) || (table->expansion[level] == BND));
			if (newKeysTotal == newKeysTotal1) {
				expn = expn1;
			} else if (newKeysTotal == newKeysTotal2) {
				expn = expn2;
			} else {
				expn = expn3;
			}
			double key = newKeysTotal;
			double keyNew = oldKeysTotal * table->choose_new_bound_factor;
			double keyDav = oldKeysTotal * table->choose_dav_bound_factor;
			if ( (key >= keyNew) ||
					(!isShan(expn) && (key >= keyDav)) ) {
				if (!changeExpnBetweenSND(table,level)) {
					printf("chooseSND4inPlace: %d, roll back failed\n", level);
					goto chooseFailed;
				}
				assert((table->keys-table->isolated) == oldKeysTotal);
			} else { // BND<-BS<-CS or CS<-CND<-BND
				if (newKeysTotal == newKeysTotal1) {
					if (!changeExpnBetweenBiCla(table,level)) {
						printf("chooseSND4inPlace: %d, roll back failed\n", level);
						goto chooseFailed;
					}
					assert((table->keys-table->isolated) == newKeysTotal2);
					if (!changeExpnBetweenSND(table,level)) {
						printf("chooseSND4inPlace: %d, roll back failed\n", level);
						goto chooseFailed;
					}
					assert((table->keys-table->isolated) == newKeysTotal1);
				} else if (newKeysTotal == newKeysTotal2) {
					if (!changeExpnBetweenBiCla(table,level)) {
						printf("chooseSND4inPlace: %d, roll back failed\n", level);
						goto chooseFailed;
					}
					assert((table->keys-table->isolated) == newKeysTotal2);
				}
			}
		}
		// re-count nonShan
		if (isShan(initExpn) && !isShan(table->expansion[level])) {
			// S => ND
			nonShan ++;
		} else if (!isShan(initExpn) && isShan(table->expansion[level])){
			// ND => S
			nonShan --;
		}
		assert(nonShan <= upper_bound);
	}

	return(1);

chooseFailed:

	fprintf(table->err, "chooseSND4inPlace failed\n");
	return(0);

} /* End of chooseSND4inPlace */
