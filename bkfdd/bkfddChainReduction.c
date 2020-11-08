/**
  @file

  @ingroup bkfdd

  @brief BKFDD RC detection, to evaluate effect of Chain Reduction rules.

  @author Xuanxiang Huang

  @copyright
  Copyright (c) 2019-, Jinan University, Guangzhou, China.

  All rights reserved.

======================================================================
	All functions are originate from cuddSymmetry.c and cuddGroup.c

	@Modification and Extension details
		1. Extend cuddSymmCheck to check positive and negative symmetric properties of BKFDDs.
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

#define AUX_REF_SIZE 500

static int Bkfdd_bS_S_RCDetection(DdManager * table, int x, int y, int * detected, int * reduced);
static int Bkfdd_bS_D_RCDetection(DdManager * table, int x, int y, int * detected, int * reduced);
static int Bkfdd_bD_S_RCDetection(DdManager * table, int x, int y, int * detected, int * reduced);
static int Bkfdd_bD_D_RCDetection(DdManager * table, int x, int y, int * detected, int * reduced);
static DdHalfWord **auxRefArray(unsigned int keys);

/*
	Chain Reduction(RC) rules are derived from positive, negative symmetry property of BDD's theory,
	whcih has been proposed	in 
		"Symmetry Detection and Dynamic Variable Ordering of Decision Diagrams",
		"Who Are the Variables in Your Neighborhood".	
	There are many applications of these properties, such as Symmetry-Sifting, Group-Sifting 
	and Linear-Sifting. 
	Since BKFDD introduce 6 different logic	expansions, one can derive variants of Symmetry property.
	It can be derived there are 6 different variants, and can be conclude into 4 structures.
	
	The application of RC will modify low, high-successors, and auxiliary function of x-nodes.
	Since DdNode structure has no space to store information of new low, high-successors,
	and new auxiliary function, we won't do any modification for nodes, but will estimate
	how many y-nodes can be reduced, and report the result. 

	Besides, there is a case where RC has no effect, if f1, f0 have external reference,
	then RC cannot reduce DD's size.

	In the following, use f1 to denote f_low, f0 denote f_high.

*/


/**
	@brief Check BKFDD bottom up, and report how many nodes can be reduced by
	Chain-Reduction(RC) rules.	
*/
int
Bkfdd_RC_Detection(
	DdManager * table,
	int * detected,
	int * reduced)
{
	int interactNull, i;
	if (table->interact == NULL) {
		int res = cuddInitInteract(table);
		if (res == 0) return(0);
		interactNull = 1;
	} else {
		interactNull = 0;
	}
	for (i = table->size-2; i >= 0; i --) {
		if (isCla(table->expansion[i])) continue;
		if (cuddTestInteract(table,table->invperm[i],table->invperm[i+1])) {
			int xdec = table->expansion[i];
			int ydec = table->expansion[i+1];
			int RCdetect = 0; int RCreduce = 0;
			if (isShan(xdec)) {
				if (isShan(ydec)) {
					if (!Bkfdd_bS_S_RCDetection(table,i,i+1,&RCdetect,&RCreduce))
						goto detectFailed;
				} else {
					if (!Bkfdd_bS_D_RCDetection(table,i,i+1,&RCdetect,&RCreduce))
						goto detectFailed;
				}
			} else {
				if (isShan(ydec)) {
					if (!Bkfdd_bD_S_RCDetection(table,i,i+1,&RCdetect,&RCreduce))
						goto detectFailed;
				} else {
					if (!Bkfdd_bD_D_RCDetection(table,i,i+1,&RCdetect,&RCreduce))
						goto detectFailed;
				}
			}
			*detected += RCdetect;
			*reduced += RCreduce;
		}
	}

	if (interactNull) {
		FREE(table->interact);
	}
	return(1);

detectFailed:

	if (interactNull) {
		FREE(table->interact);
	}
	return(0);

} /* end of Bkfdd_RC_Detection */


/** 
	@brief bS-*S RC dectection. *S denote S or bS
	
	@details Checking condition is (f11 == f00) && (f10 == f01), if condition holds,
	deref f1 and f0, if reference count of f1(f0) decrease to 0, then f1(f0) can be reduced.
	Report how many nodes can be reduced.

	NOTE: Make sure there are no dead nodes.

*/
static int
Bkfdd_bS_S_RCDetection(
  DdManager * table,
  int  x,
  int  y,
	int * detected,
	int * reduced)
{

  DdNode *f,*f0,*f1,*f01,*f00,*f11,*f10,*one;
  int comple;		/* f0 is complemented */
  int yindex;
  int i;
  DdNodePtr *list;
  int slots;
  DdNode *sentinel = &(table->sentinel);

	assert( isBi(table->expansion[x]) &&
					isShan(table->expansion[x]) &&
					isShan(table->expansion[y]) );

	if ( (table->subtables[x].keys == 0) || 
				(table->subtables[y].keys == 0) ) {
		return(0);
	}

	int RCdetect = 0; int RCreduce = 0;

	yindex = table->invperm[y];

	/* 
		1. Traverse all y-nodes and store refCount.
		2. Traverse all y-nodes if checking condition holds, increase detect counter
			and decrease refCount. If refCount equal to 0, then reduce this node has 
			effect on DD size, increase reduce counter.
		3. Recover all y-nodes refCount.
	*/
	DdHalfWord **refArray = auxRefArray(table->subtables[y].keys);
	if (refArray == NULL) {
		return(0);
	}
	int idx1, idx2;
	idx1 = idx2 = 0;
	slots = table->subtables[y].slots;
	list = table->subtables[y].nodelist;
	for (i = 0; i < slots; i ++) {
		f = list[i];
		while (f != sentinel) {
			if (f->ref == 0) goto checkFailed;
			refArray[idx1][idx2 ++] = f->ref;
			f = f->next;
			if (idx2 == AUX_REF_SIZE) {
				idx1 ++;
				idx2 = 0;
			}
		}
	}

	one = DD_ONE(table);
	unsigned int initKeysTotal = table->keys-table->isolated;

	slots = table->subtables[x].slots;
	list = table->subtables[x].nodelist;
	for (i = 0; i < slots; i++) {
		f = list[i];
		while (f != sentinel) {
			/* Find f1, f0, f11, f10, f01, f00. */
			f1 = cuddT(f);
			f0 = Cudd_Regular(cuddE(f));
			if (f1 == one || f0 == one ||
					(int)f1->index != yindex || (int)f0->index != yindex) {
				// impossible case
				f = f->next;
				continue;
			}

			if ( (f1->ref == 0) || (f0->ref == 0) ) goto checkFailed;

			comple = Cudd_IsComplement(cuddE(f));
			f11 = cuddT(f1); f10 = cuddE(f1);
			f01 = cuddT(f0); f00 = cuddE(f0);
			if (comple) {
				f01 = Cudd_Not(f01);
				f00 = Cudd_Not(f00);
			}

			if ( (f11 == f00) && (f01 == f10) ) {
				RCdetect += 2;
				cuddDeref(f1);
				cuddDeref(f0);
				if (f1->ref == 0) {
					RCreduce ++;
				}
				if (f0->ref == 0) {
					RCreduce ++;
				}
			}

			f = f->next;
		} /* while */
	} /* for */
	
	idx1 = idx2 = 0;
	slots = table->subtables[y].slots;
	list = table->subtables[y].nodelist;
	for (i = 0; i < slots; i ++) {
		f = list[i];
		while (f != sentinel) {
			f->ref = refArray[idx1][idx2 ++];
			f = f->next;
			if (idx2 == AUX_REF_SIZE) {
				idx1 ++;
				idx2 = 0;
			}
		}
	}
	FREE(refArray);

	*detected = RCdetect;
	*reduced = RCreduce;

	unsigned int totalKeys = table->keys-table->isolated;
	assert(totalKeys == initKeysTotal);	

	return(1);

checkFailed:

	FREE(refArray);
	return(0);

} /* end of Bkfdd_bS_S_RCDetection */


/** 
	@brief S-D RC detection.

	@details Checking condition is (f11 \xor f01 == f10) && (f10 == f00), if condition holds,
	deref f1 and f0, if reference count of f1(f0) decrease to 0, then f1(f0) can be reduced.
	Report how many nodes can be reduced.

*/
static int
Bkfdd_bS_D_RCDetection(
  DdManager * table,
  int  x,
  int  y,
	int * detected,
	int * reduced)
{

  DdNode *f,*f0,*f1,*f01,*f00,*f11,*f10,*one,*tmp,*next;
	DdNodePtr *previousP = NULL;
  int comple;		/* f0 is complemented */
  int yindex;
  int i, k;
  DdNodePtr *list;
  int slots;
  DdNode *sentinel = &(table->sentinel);

	assert( isBi(table->expansion[x]) &&
				isShan(table->expansion[x]) &&
				!isShan(table->expansion[y]) );

	if ( (table->subtables[x].keys == 0) || 
				(table->subtables[y].keys == 0) ) {
		return(0);
	}

	int RCdetect = 0; int RCreduce = 0;

	yindex = table->invperm[y];

	/* 
		1. Traverse all y-nodes and store refCount.
		2. Traverse all y-nodes if checking condition holds, increase detect counter
			and decrease refCount. If refCount equal to 0, then reduce this node has 
			effect on DD size, increase reduce counter.
		3. Recover all y-nodes refCount.
	*/
	DdHalfWord **refArray = auxRefArray(table->subtables[y].keys);
	if (refArray == NULL) {
		return(0);
	}
	int idx1, idx2;
	idx1 = idx2 = 0;
	slots = table->subtables[y].slots;
	list = table->subtables[y].nodelist;
	for (i = 0; i < slots; i ++) {
		f = list[i];
		while (f != sentinel) {
			if (f->ref == 0) goto checkFailed;
			refArray[idx1][idx2 ++] = f->ref;
			f = f->next;
			if (idx2 == AUX_REF_SIZE) {
				idx1 ++;
				idx2 = 0;
			}
		}
	}

	one = DD_ONE(table);
	unsigned int initKeysTotal = table->keys-table->isolated;

	slots = table->subtables[x].slots;
	list = table->subtables[x].nodelist;
	for (i = 0; i < slots; i++) {
		f = list[i];
		while (f != sentinel) {
			/* Find f1, f0, f11, f10, f01, f00. */
			f1 = cuddT(f);
			f0 = Cudd_Regular(cuddE(f));
			if (f1 == one || f0 == one ||
					(int)f1->index != yindex || (int)f0->index != yindex) {
				// impossible case
				f = f->next;
				continue;
			}

			if ( (f1->ref == 0) || (f0->ref == 0) ) goto checkFailed;

			comple = Cudd_IsComplement(cuddE(f));
			f11 = cuddT(f1); f10 = cuddE(f1);
			f01 = cuddT(f0); f00 = cuddE(f0);
			if (comple) {
				f01 = Cudd_Not(f01);
			}
			if (f10 != f00) {
				// impossible case
				f= f->next;
				continue;
			}

			tmp = BkfddXorRecur_Inner(table,f11,f01);
			if (tmp == f00) {
				RCdetect += 2;
				cuddDeref(f1);
				cuddDeref(f0);
				if (f1->ref == 0) {
					RCreduce ++;
				}
				if (f0->ref == 0) {
					RCreduce ++;
				}
			}
			
			f = f->next;
		} /* while */
	} /* for */
	
	idx1 = idx2 = 0;
	slots = table->subtables[y].slots;
	list = table->subtables[y].nodelist;
	for (i = 0; i < slots; i ++) {
		f = list[i];
		while (f != sentinel) {
			f->ref = refArray[idx1][idx2 ++];
			f = f->next;
			if (idx2 == AUX_REF_SIZE) {
				idx1 ++;
				idx2 = 0;
			}
		}
	}
	FREE(refArray);

	// clean cache and gc subtables below y-level
	cuddCacheFlush(table);
	cuddLocalCacheClearAll(table);
	for (i = y+1; (int)i < table->size; i++) {
		DdNodePtr *nodelist = table->subtables[i].nodelist;
		slots = table->subtables[i].slots;
		for (k = 0; k < slots; k ++) {
			previousP = &(nodelist[k]);
			f = *previousP;
			while (f != sentinel) {
				next = f->next;
				if (f->ref == 0) {
					tmp = cuddT(f);
					cuddSatDec(tmp->ref);
					tmp = Cudd_Regular(cuddE(f));
					cuddSatDec(tmp->ref);
					cuddDeallocNode(table,f);
					table->subtables[i].keys--;
					table->keys --;
				} else {
					*previousP = f;
					previousP = &(f->next);
				}
				f = next;
			}
			*previousP = sentinel;
		}
	}

	unsigned int totalKeys = table->keys-table->isolated;
	assert(totalKeys == initKeysTotal);

	*detected = RCdetect;
	*reduced = RCreduce;

	return(1);

checkFailed:

	FREE(refArray);
	return(0);

} /* end of Bkfdd_bS_D_RCDetection */


/** 
	@brief D-S RC detection.

	@details Checking condition is f11 \xor f10 == f0, if condition holds,
	deref f1, if reference count of f1 decrease to 0, then f1 can be reduced.
	Report how many nodes can be reduced.

*/
static int
Bkfdd_bD_S_RCDetection(
  DdManager * table,
  int  x,
  int  y,
	int * detected,
	int * reduced)
{

  DdNode *f,*f0,*f1,*f11,*f10,*tmp,*next,*one;
	DdNodePtr *previousP = NULL;
  int yindex;
  int i, k;
  DdNodePtr *list;
  int slots;
  DdNode *sentinel = &(table->sentinel);

	assert( isBi(table->expansion[x]) &&
			!isShan(table->expansion[x]) &&
			isShan(table->expansion[y]) );

	if ( (table->subtables[x].keys == 0) || 
				(table->subtables[y].keys == 0) ) {
		return(0);
	}

	int RCdetect = 0; int RCreduce = 0;

	yindex = table->invperm[y];

	/* 
		1. Traverse all y-nodes and store refCount.
		2. Traverse all y-nodes if checking condition holds, increase detect counter
			and decrease refCount. If refCount equal to 0, then reduce this node has 
			effect on DD size, increase reduce counter.
		3. Recover all y-nodes refCount.
	*/
	DdHalfWord **refArray = auxRefArray(table->subtables[y].keys);
	if (refArray == NULL) {
		return(0);
	}
	int idx1, idx2;
	idx1 = idx2 = 0;
	slots = table->subtables[y].slots;
	list = table->subtables[y].nodelist;
	for (i = 0; i < slots; i ++) {
		f = list[i];
		while (f != sentinel) {
			if (f->ref == 0) goto checkFailed;
			refArray[idx1][idx2 ++] = f->ref;
			f = f->next;
			if (idx2 == AUX_REF_SIZE) {
				idx1 ++;
				idx2 = 0;
			}
		}
	}

	one = DD_ONE(table);
	unsigned int initKeysTotal = table->keys-table->isolated;

	slots = table->subtables[x].slots;
	list = table->subtables[x].nodelist;
	for (i = 0; i < slots; i++) {
		f = list[i];
		while (f != sentinel) {
			f1 = cuddT(f);
			f0 = Cudd_Regular(cuddE(f));
			if ( f1 == one || (int)f1->index != yindex ||
					(f0 != one && (int)f0->index == yindex) ) {
				f = f->next;
				continue;
			}

			if ( (f1->ref == 0) || (f0->ref == 0) ) goto checkFailed;

			f11 = cuddT(f1); f10 = cuddE(f1);

			tmp = BkfddXorRecur_Inner(table,f11,f10);
			if (tmp == cuddE(f)) {
				RCdetect += 1;
				cuddDeref(f1);
				if (f1->ref == 0) {
					RCreduce ++;
				}
			}

			f = f->next;
		} /* while */
	} /* for */

	idx1 = idx2 = 0;
	slots = table->subtables[y].slots;
	list = table->subtables[y].nodelist;
	for (i = 0; i < slots; i ++) {
		f = list[i];
		while (f != sentinel) {
			f->ref = refArray[idx1][idx2 ++];
			f = f->next;
			if (idx2 == AUX_REF_SIZE) {
				idx1 ++;
				idx2 = 0;
			}
		}
	}
	FREE(refArray);

	// clean cache and gc subtables below y-level
	cuddCacheFlush(table);
	cuddLocalCacheClearAll(table);
	for (i = y+1; (int)i < table->size; i++) {
		DdNodePtr *nodelist = table->subtables[i].nodelist;
		slots = table->subtables[i].slots;
		for (k = 0; k < slots; k ++) {
			previousP = &(nodelist[k]);
			f = *previousP;
			while (f != sentinel) {
				next = f->next;
				if (f->ref == 0) {
					tmp = cuddT(f);
					cuddSatDec(tmp->ref);
					tmp = Cudd_Regular(cuddE(f));
					cuddSatDec(tmp->ref);
					cuddDeallocNode(table,f);
					table->subtables[i].keys--;
					table->keys --;
				} else {
					*previousP = f;
					previousP = &(f->next);
				}
				f = next;
			}
			*previousP = sentinel;
		}
	}
	
	unsigned int totalKeys = table->keys-table->isolated;
	assert(totalKeys == initKeysTotal);

	*detected = RCdetect;
	*reduced = RCreduce;

	return(1);

checkFailed:

	FREE(refArray);
	return(0);

} /* end of Bkfdd_bD_S_RCDetection */


/** 
	@brief D-D RC detection.

	@details Checking condition is f10 == f0, if condition holds,
	deref f1, if reference count of f1 decrease to 0, then f1 can be reduced.
	Report how many nodes can be reduced.

*/
static int
Bkfdd_bD_D_RCDetection(
  DdManager * table,
  int  x,
  int  y,
	int * detected,
	int * reduced)
{

  DdNode *f,*f0,*f1,*f10,*one;
  int yindex;
  int i;
  DdNodePtr *list;
  int slots;
  DdNode *sentinel = &(table->sentinel);

	assert( isBi(table->expansion[x]) &&
			!isShan(table->expansion[x]) &&
			!isShan(table->expansion[y]) );

	if ( (table->subtables[x].keys == 0) || 
				(table->subtables[y].keys == 0) ) {
		return(0);
	}

	int RCdetect = 0; int RCreduce = 0;

	yindex = table->invperm[y];

	/* 
		1. Traverse all y-nodes and store refCount.
		2. Traverse all y-nodes if checking condition holds, increase detect counter
			and decrease refCount. If refCount equal to 0, then reduce this node has 
			effect on DD size, increase reduce counter.
		3. Recover all y-nodes refCount.
	*/
	DdHalfWord **refArray = auxRefArray(table->subtables[y].keys);
	if (refArray == NULL) {
		return(0);
	}
	int idx1, idx2;
	idx1 = idx2 = 0;
	slots = table->subtables[y].slots;
	list = table->subtables[y].nodelist;
	for (i = 0; i < slots; i ++) {
		f = list[i];
		while (f != sentinel) {
			if (f->ref == 0) goto checkFailed;
			refArray[idx1][idx2 ++] = f->ref;
			f = f->next;
			if (idx2 == AUX_REF_SIZE) {
				idx1 ++;
				idx2 = 0;
			}
		}
	}

	one = DD_ONE(table);
	unsigned int initKeysTotal = table->keys-table->isolated;

	slots = table->subtables[x].slots;
	list = table->subtables[x].nodelist;
	for (i = 0; i < slots; i++) {
		f = list[i];
		while (f != sentinel) {
			f1 = cuddT(f);
			f0 = Cudd_Regular(cuddE(f));
			if ( f1 == one || (int)f1->index != yindex ||
					(f0 != one && (int)f0->index == yindex) ) {
				f = f->next;
				continue;
			}

			if ( (f1->ref == 0) || (f0->ref == 0) ) goto checkFailed;

			f10 = cuddE(f1);
			if (f10 == cuddE(f)) {
				cuddDeref(f1);
				RCdetect += 1;
				if (f1->ref == 0) {
					RCreduce ++;
				}
			}

			f = f->next;
		} /* while */
	} /* for */
	
	idx1 = idx2 = 0;
	slots = table->subtables[y].slots;
	list = table->subtables[y].nodelist;
	for (i = 0; i < slots; i ++) {
		f = list[i];
		while (f != sentinel) {
			f->ref = refArray[idx1][idx2 ++];
			f = f->next;
			if (idx2 == AUX_REF_SIZE) {
				idx1 ++;
				idx2 = 0;
			}
		}
	}
	FREE(refArray);

	unsigned int totalKeys = table->keys-table->isolated;
	assert(totalKeys == initKeysTotal);

	*detected = RCdetect;
	*reduced = RCreduce;

	return(1);

checkFailed:

	FREE(refArray);
	return(0);

} /* end of Bkfdd_bD_D_RCDetection */


/** 
	@brief Auxiliary array to store reference count.

	@details Alloc a auxiliary array and return.

*/
static 
DdHalfWord **auxRefArray(
	unsigned int keys)
{
	if (keys == 0)	return(NULL);
	int i,j,n;
	if (keys % AUX_REF_SIZE == 0) {
		n = keys / AUX_REF_SIZE;
	} else {
		n = keys / AUX_REF_SIZE + 1;
	}
	DdHalfWord **refArray = ALLOC(DdHalfWord *,n);
	if (refArray == NULL) return(NULL);
	for (i = 0; i < n; i ++) {
		refArray[i] = NULL;
		refArray[i] = ALLOC(DdHalfWord,AUX_REF_SIZE);
		if (refArray[i] == NULL) {
			for (j = 0; j < i; j ++) {
				FREE(refArray[j]);
			}
			FREE(refArray);
			return(NULL);
		}
		for (j = 0; j < AUX_REF_SIZE; j ++) {
			refArray[i][j] = 0;
		}
	}
	return(refArray);
} /* end of auxRefArray */
