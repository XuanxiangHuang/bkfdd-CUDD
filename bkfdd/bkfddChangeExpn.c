/**
  @file

  @ingroup bkfdd

  @brief Functions for changing expansion types of BKFDD.

  @author Xuanxiang Huang

  @copyright
  Copyright (c) 2019-, Jinan University, Guangzhou, China.

  All rights reserved.

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

/*********************************************************************************
	Expansion types change, manually gc, the performs of this version is correct, 
	but results are sometime unpredictable, currently don't know why.
*********************************************************************************/

static void changeExpnPostProcess(DdManager *dd, int level);

/**
	@brief Change expansion type of given level.
	BS <==> BND, or CS <==> CND.

	1. Disable auto reordering and garbage collecting.
	2. Move all nodes to a list, create new table if needed,
			otherwise use old table.
	3. For any node N of given level: 
		3.1	Apply Boolean opeartion to N's old successors,
				and generate new successors.
		3.2	Replace N's old successors by new successors.
	4. Re-compute hash value of N.
	5. Re-insert N to table.
	6. Collecting garbages.
	7. Recover auto reordering setting.

	@return 1 if success, 0 if fail.

	@sideeffect Nodes at level may violate "low-edge regular" principle.

*/
int
changeExpnBetweenSND(
	DdManager * dd,
	int level)
{
	assert(level != (dd->size-1));
	assert(!isPDavio(dd->expansion[level]));
	assert(dd->dead == 0);

	/* Disable auto reordering and garbage collecting. */
	int reorderSave = dd->autoDyn;
	dd->autoDyn = 0;
	int gcSave = dd->gcEnabled;
	dd->gcEnabled = 0;
	/* Move all nodes to a chain, create new table if needed,
	otherwise use old table. */
	DdNode *nodechain, *p, *next, *f_newh, *tmp, *f_l, *f_h;
	nodechain = p = next = f_l = f_h = f_newh = tmp = NULL;
	DdNodePtr *previousP = NULL;
	unsigned int i, posn;
	extern DD_OOMFP MMoutOfMemory;
	DD_OOMFP saveHandler;

	DdNodePtr *list = dd->subtables[level].nodelist;
	int oldkeys = dd->subtables[level].keys;
	unsigned int slots = dd->subtables[level].slots;
	int shift = dd->subtables[level].shift;
	DdNode *sentinel = &(dd->sentinel);
	int dec = dd->expansion[level];
	/* Empty current nodelist, put them to nodechain. */
	for (i = 0; i < slots; i++) {
		p = list[i];
		while (p != sentinel) {
			next = p->next;
			p->next = nodechain;
			nodechain = p;
			p = next;
		} /* while there are elements in the collision chain */
	} /* for each slot of the subtable */
	DdNode *zero = Cudd_Not(DD_ONE(dd));

	if (((unsigned) oldkeys >= slots || (unsigned) slots == dd->initSlots) &&
	(unsigned)oldkeys <= DD_MAX_SUBTABLE_DENSITY * slots) {
	/* Use old table. Do nothing. */
	} else {
	/* Create new table. The number of keys unchanged. */
		DdNodePtr *newlist = NULL;
		unsigned int newslots = slots;
		int newshift = shift;
		while ((unsigned) oldkeys > DD_MAX_SUBTABLE_DENSITY * newslots) {
			newshift--;
			newslots <<= 1;
		}
		while ((unsigned) oldkeys < newslots &&
		newslots > dd->initSlots) {
			newshift++;
			newslots >>= 1;
		}
		/* Try to allocate new table. Be ready to back off. */
		saveHandler = MMoutOfMemory;
		MMoutOfMemory = dd->outOfMemCallback;
		newlist = ALLOC(DdNodePtr, newslots);
		MMoutOfMemory = saveHandler;
		if (newlist == NULL) {
			(void) fprintf(dd->err, "changeExpnBetweenSND: create subtable lack of memory\n");
			return(0);
		} else {
			dd->slots += ((int) newslots - slots);
			dd->minDead = (unsigned)
			(dd->gcFrac * (double) dd->slots);
			dd->cacheSlack = (int)
			ddMin(dd->maxCacheHard, DD_MAX_CACHE_TO_SLOTS_RATIO
			* dd->slots) - 2 * (int) dd->cacheSlots;
			dd->memused +=
			((int) newslots - slots) * sizeof(DdNodePtr);
			FREE(list);
			slots =  newslots;
			shift = newshift;
			list = newlist;

			dd->subtables[level].nodelist = list;
			dd->subtables[level].slots = slots;
			dd->subtables[level].shift = shift;
			dd->subtables[level].maxKeys = slots * DD_MAX_SUBTABLE_DENSITY;
		}
	}

	/* Initialize new subtable. */
	for (i = 0; i < slots; i++) {
		list[i] = sentinel;
	}
	/* Replace successors of nodes in the given level. */
	while (nodechain != NULL) {
		next = nodechain->next;
		f_l = cuddT(nodechain);
		f_h = cuddE(nodechain);
		if (isShan(dec)) { // S => ND
			assert(f_l != f_h);
		} else { // ND => S
			assert(f_h != zero);
		}
		f_newh = BkfddXorRecur_Inner(dd, f_l, f_h);
		if (f_newh == NULL) {
			/* Compute new high successor failed, out of memory. */
			(void) fprintf(dd->err, "changeExpnBetweenSND: compute new high lack of memory\n");
			return(0);
		}
		cuddRef(f_newh);
		cuddDeref(f_h);
		cuddE(nodechain) = f_newh;
		if (isShan(dec)) { // S => ND
			assert(f_newh != zero);
		} else { // ND => S
			assert(f_l != f_newh);	
		}
		/* Re-compute hash value, and re-insert to subtable. */
		posn = ddHash(f_l, f_newh, shift);
		previousP = &(list[posn]);
		tmp = *previousP;
		while (f_l < cuddT(tmp)) {
			previousP = &(tmp->next);
			tmp = *previousP;
		}
		while (f_l == cuddT(tmp) && f_newh < cuddE(tmp)) {
			previousP = &(tmp->next);
			tmp = *previousP;
		}
		nodechain->next = *previousP;
		*previousP = nodechain;
		nodechain = next;
	}

	if (dec == CS) 				{ dd->expansion[level] = CND; }
	else if (dec == BS) 	{ dd->expansion[level] = BND; }
	else if (dec == CND) 	{ dd->expansion[level] = CS; }
	else if (dec == BND)	{ dd->expansion[level] = BS; }

	/* clear cache, gc and recounting isolated projection functions */
	changeExpnPostProcess(dd,level+1);

	/* Recover dynamic reordering setting. */
	dd->autoDyn = reorderSave;
	dd->gcEnabled = gcSave;

	return(1);
}	/* end of changeExpnBetweenSND */


/**
	@brief Change expansion type of given level.
	BND <==> BPD, or CND <==> CPD.

	1. Disable auto reordering and garbage collecting.
	2. Move all nodes to a list, create new table if needed,
			otherwise use old table.
	3. For any node N of given level: 
		3.1	Apply Boolean opeartion to N's old successors,
				and generate new successors.
		3.2	Replace N's old successors by new successors.
	4. Re-compute hash value of N.
	5. Re-insert N to table.
	6. Collecting garbages.
	7. Recover auto reordering setting.

	@return 1 if success, 0 if fail.

	@sideeffect Nodes at level may violate "low-edge regular" principle.

*/
int
changeExpnBetweenNDPD(
	DdManager * dd,
	int level)
{
	assert(level != (dd->size-1));
	assert(!isShan(dd->expansion[level]));
	assert(dd->dead == 0);
	
	/* Disable auto reordering and garbage collecting. */
	int reorderSave = dd->autoDyn;
	dd->autoDyn = 0;
	int gcSave = dd->gcEnabled;
	dd->gcEnabled = 0;
	/* Move all nodes to a chain, create new table if needed,
	otherwise use old table. */
	DdNode *nodechain, *p, *next, *f_newl, *tmp, *f_l, *f_h;
	nodechain = p = next = f_l = f_h = f_newl = tmp = NULL;
	DdNodePtr *previousP = NULL;
	unsigned int i, posn;
	extern DD_OOMFP MMoutOfMemory;
	DD_OOMFP saveHandler;

	DdNodePtr *list = dd->subtables[level].nodelist;
	int oldkeys = dd->subtables[level].keys;
	unsigned int slots = dd->subtables[level].slots;
	int shift = dd->subtables[level].shift;
	DdNode *sentinel = &(dd->sentinel);
	int dec = dd->expansion[level];
	/* Empty current nodelist, put them to nodechain. */
	for (i = 0; i < slots; i++) {
		p = list[i];
		while (p != sentinel) {
			next = p->next;
			p->next = nodechain;
			nodechain = p;
			p = next;
		} /* while there are elements in the collision chain */
	} /* for each slot of the subtable */
	DdNode *zero = Cudd_Not(DD_ONE(dd));
	if (((unsigned) oldkeys >= slots || (unsigned) slots == dd->initSlots) &&
	(unsigned)oldkeys <= DD_MAX_SUBTABLE_DENSITY * slots) {
	/* Use old table. Do nothing. */
	} else {
	/* Create new table. The number of keys unchanged. */
		DdNodePtr *newlist = NULL;
		unsigned int newslots = slots;
		int newshift = shift;
		while ((unsigned) oldkeys > DD_MAX_SUBTABLE_DENSITY * newslots) {
			newshift--;
			newslots <<= 1;
		}
		while ((unsigned) oldkeys < newslots &&
		newslots > dd->initSlots) {
			newshift++;
			newslots >>= 1;
		}
		/* Try to allocate new table. Be ready to back off. */
		saveHandler = MMoutOfMemory;
		MMoutOfMemory = dd->outOfMemCallback;
		newlist = ALLOC(DdNodePtr, newslots);
		MMoutOfMemory = saveHandler;
		if (newlist == NULL) {
			(void) fprintf(dd->err, "changeExpnBetweenNDPD: create subtable lack of memory\n");
			return(0);
		} else {
			dd->slots += ((int) newslots - slots);
			dd->minDead = (unsigned)
			(dd->gcFrac * (double) dd->slots);
			dd->cacheSlack = (int)
			ddMin(dd->maxCacheHard, DD_MAX_CACHE_TO_SLOTS_RATIO
			* dd->slots) - 2 * (int) dd->cacheSlots;
			dd->memused +=
			((int) newslots - slots) * sizeof(DdNodePtr);
			FREE(list);
			slots =  newslots;
			shift = newshift;
			list = newlist;

			dd->subtables[level].nodelist = list;
			dd->subtables[level].slots = slots;
			dd->subtables[level].shift = shift;
			dd->subtables[level].maxKeys = slots * DD_MAX_SUBTABLE_DENSITY;
		}
	}
	/* Initialize new subtable. */
	for (i = 0; i < slots; i++) {
		list[i] = sentinel;
	}
	/* Replace successors of nodes in the given level. */
	while (nodechain != NULL) {
		next = nodechain->next;
		f_l = cuddT(nodechain);
		f_h = cuddE(nodechain);
		assert(f_h != zero);
		/* f_newl = f_l XOR f_h, f_newh = f_h */
		f_newl = BkfddXorRecur_Inner(dd, f_l, f_h);
		if (f_newl == NULL) {
			/* Compute new high successor failed, out of memory. */
			(void) fprintf(dd->err, "changeExpnBetweenNDPD: compute new low lack of memory\n");
			return(0);
		}
		cuddRef(f_newl);
		cuddDeref(f_l);
		/* New low-successor may complemented, which makes node non-canonical. 
			Need a procedure to fix canonicity. */
		cuddT(nodechain) = f_newl;

		/* Re-compute hash value, and re-insert to subtable. */
		posn = ddHash(f_newl, f_h, shift);
		previousP = &(list[posn]);
		tmp = *previousP;
		while (f_newl < cuddT(tmp)) {
			previousP = &(tmp->next);
			tmp = *previousP;
		}
		while (f_newl == cuddT(tmp) && f_h < cuddE(tmp)) {
			previousP = &(tmp->next);
			tmp = *previousP;
		}
		nodechain->next = *previousP;
		*previousP = nodechain;
		nodechain = next;
	}

	if (dec == CPD) 			{ dd->expansion[level] = CND; }
	else if (dec == BPD) 	{ dd->expansion[level] = BND; }
	else if (dec == CND) 	{ dd->expansion[level] = CPD; }
	else if (dec == BND)	{ dd->expansion[level] = BPD; }

	/* clear cache, gc and recounting isolated projection functions */
	changeExpnPostProcess(dd,level+1);

	/* Recover dynamic reordering setting. */
	dd->autoDyn = reorderSave;
	dd->gcEnabled = gcSave;

	return(1);
}	/* end of changeExpnBetweenNDPD */


/**
	@brief Change expansion types, CPD => CS or BPD => BS
	at internal level.

	1. Disable auto reordering and garbage collecting.
	2. Move all nodes to a list, create new table if needed,
			otherwise use old table.
	3. For any node N of given level: 
		3.1	Apply Boolean opeartion to N's old successors,
				and generate new successors.
		3.2	Replace N's old successors by new successors.
	4. Re-compute hash value of N.
	5. Re-insert N to table.
	6. Collecting garbages.
	7. Recover auto reordering setting.

	@return 1 if success, 0 if fail.

	@sideeffect Nodes at level may violate "low-edge regular" principle.

*/
int
changeExpnPDtoS(
	DdManager * dd,
	int level)
{
	assert(level != (dd->size-1));
	assert(isPDavio(dd->expansion[level]));
	assert(dd->dead == 0);
	
	/* Disable auto reordering and garbage collecting. */
	int reorderSave = dd->autoDyn;
	dd->autoDyn = 0;
	int gcSave = dd->gcEnabled;
	dd->gcEnabled = 0;
	/* Move all nodes to a chain, create new table if needed,
	otherwise use old table. */
	DdNode *nodechain, *p, *next, *f_newl, *tmp, *f_l, *f_h;
	nodechain = p = next = f_l = f_h = f_newl = tmp = NULL;
	DdNodePtr *previousP = NULL;
	unsigned int i, posn;
	extern DD_OOMFP MMoutOfMemory;
	DD_OOMFP saveHandler;

	DdNodePtr *list = dd->subtables[level].nodelist;
	int oldkeys = dd->subtables[level].keys;
	unsigned int slots = dd->subtables[level].slots;
	int shift = dd->subtables[level].shift;
	DdNode *sentinel = &(dd->sentinel);
	int dec = dd->expansion[level];
	/* Empty current nodelist, put them to nodechain. */
	for (i = 0; i < slots; i++) {
		p = list[i];
		while (p != sentinel) {
			next = p->next;
			p->next = nodechain;
			nodechain = p;
			p = next;
		} /* while there are elements in the collision chain */
	} /* for each slot of the subtable */
	DdNode *zero = Cudd_Not(DD_ONE(dd));
	if (((unsigned) oldkeys >= slots || (unsigned) slots == dd->initSlots) &&
	(unsigned)oldkeys <= DD_MAX_SUBTABLE_DENSITY * slots) {
	/* Use old table. Do nothing. */
	} else {
	/* Create new table. The number of keys unchanged. */
		DdNodePtr *newlist = NULL;
		unsigned int newslots = slots;
		int newshift = shift;
		while ((unsigned) oldkeys > DD_MAX_SUBTABLE_DENSITY * newslots) {
			newshift--;
			newslots <<= 1;
		}
		while ((unsigned) oldkeys < newslots &&
		newslots > dd->initSlots) {
			newshift++;
			newslots >>= 1;
		}
		/* Try to allocate new table. Be ready to back off. */
		saveHandler = MMoutOfMemory;
		MMoutOfMemory = dd->outOfMemCallback;
		newlist = ALLOC(DdNodePtr, newslots);
		MMoutOfMemory = saveHandler;
		if (newlist == NULL) {
			(void) fprintf(dd->err, "changeExpnPDtoS: create subtable lack of memory\n");
			return(0);
		} else {
			dd->slots += ((int) newslots - slots);
			dd->minDead = (unsigned)
			(dd->gcFrac * (double) dd->slots);
			dd->cacheSlack = (int)
			ddMin(dd->maxCacheHard, DD_MAX_CACHE_TO_SLOTS_RATIO
			* dd->slots) - 2 * (int) dd->cacheSlots;
			dd->memused +=
			((int) newslots - slots) * sizeof(DdNodePtr);
			FREE(list);
			slots =  newslots;
			shift = newshift;
			list = newlist;

			dd->subtables[level].nodelist = list;
			dd->subtables[level].slots = slots;
			dd->subtables[level].shift = shift;
			dd->subtables[level].maxKeys = slots * DD_MAX_SUBTABLE_DENSITY;
		}
	}
	/* Initialize new subtable. */
	for (i = 0; i < slots; i++) {
		list[i] = sentinel;
	}
	/* Replace successors of nodes in the given level. */
	while (nodechain != NULL) {
		next = nodechain->next;
		f_l = cuddT(nodechain);
		f_h = cuddE(nodechain);
		assert(f_h != zero);
		/* f_newl = f_l XOR f_h; f_newh = f_l. */
		f_newl = BkfddXorRecur_Inner(dd, f_l, f_h);
		if (f_newl == NULL) {
			/* Compute new high successor failed, out of memory. */
			(void) fprintf(dd->err, "changeExpnPDtoS: compute new low lack of memory\n");
			return(0);
		}
		cuddRef(f_newl);
		cuddDeref(f_h);
		/* new low may vioalte "low-edge uncomplemented". */
		cuddT(nodechain) = f_newl;
		cuddE(nodechain) = f_l;
		assert(f_newl != f_l);
		/* Re-compute hash value, and re-insert to subtable. */
		posn = ddHash(f_newl, f_l, shift);
		previousP = &(list[posn]);
		tmp = *previousP;
		while (f_newl < cuddT(tmp)) {
			previousP = &(tmp->next);
			tmp = *previousP;
		}
		while (f_newl == cuddT(tmp) && f_l < cuddE(tmp)) {
			previousP = &(tmp->next);
			tmp = *previousP;
		}
		nodechain->next = *previousP;
		*previousP = nodechain;
		nodechain = next;
	}

	if (dec == CPD) 	{ dd->expansion[level] = CS; }
	else if (dec == BPD)	{ dd->expansion[level] = BS; }

	/* clear cache, gc and recounting isolated projection functions */
	changeExpnPostProcess(dd,level+1);

	/* Recover dynamic reordering setting. */
	dd->autoDyn = reorderSave;
	dd->gcEnabled = gcSave;

	return(1);
}	/* end of changeExpnPDtoS */


/**
	@brief Change expansion types, CS => CPD or BS => BPD,
	at internal level.

	1. Disable auto reordering and garbage collecting.
	2. Move all nodes to a list, create new table if needed,
			otherwise use old table.
	3. For any node N of given level: 
		3.1	Apply Boolean opeartion to N's old successors,
				and generate new successors.
		3.2	Replace N's old successors by new successors.
	4. Re-compute hash value of N.
	5. Re-insert N to table.
	6. Collecting garbages.
	7. Recover auto reordering setting.

	@return 1 if success, 0 if fail.

	@sideeffect Nodes at level may violate "low-edge regular" principle.

*/
int
changeExpnStoPD(
	DdManager * dd,
	int level)
{
	assert(level != (dd->size-1));
	assert(isShan(dd->expansion[level]));
	assert(dd->dead == 0);
	
	/* Disable auto reordering and garbage collecting. */
	int reorderSave = dd->autoDyn;
	dd->autoDyn = 0;
	int gcSave = dd->gcEnabled;
	dd->gcEnabled = 0;
	/* Move all nodes to a chain, create new table if needed,
	otherwise use old table. */
	DdNode *nodechain, *p, *next, *f_newh, *tmp, *f_l, *f_h;
	nodechain = p = next = f_l = f_h = f_newh = tmp = NULL;
	DdNodePtr *previousP = NULL;
	unsigned int i, posn;
	extern DD_OOMFP MMoutOfMemory;
	DD_OOMFP saveHandler;

	DdNodePtr *list = dd->subtables[level].nodelist;
	int oldkeys = dd->subtables[level].keys;
	unsigned int slots = dd->subtables[level].slots;
	int shift = dd->subtables[level].shift;
	DdNode *sentinel = &(dd->sentinel);
	int dec = dd->expansion[level];

	/* Empty current nodelist, put them to nodechain. */
	for (i = 0; i < slots; i++) {
		p = list[i];
		while (p != sentinel) {
			next = p->next;
			p->next = nodechain;
			nodechain = p;
			p = next;
		} /* while there are elements in the collision chain */
	} /* for each slot of the subtable */
	DdNode *zero = Cudd_Not(DD_ONE(dd));
	if (((unsigned) oldkeys >= slots || (unsigned) slots == dd->initSlots) &&
	(unsigned)oldkeys <= DD_MAX_SUBTABLE_DENSITY * slots) {
	/* Use old table. Do nothing. */
	} else {
	/* Create new table. The number of keys unchanged. */
		DdNodePtr *newlist = NULL;
		unsigned int newslots = slots;
		int newshift = shift;
		while ((unsigned) oldkeys > DD_MAX_SUBTABLE_DENSITY * newslots) {
			newshift--;
			newslots <<= 1;
		}
		while ((unsigned) oldkeys < newslots &&
		newslots > dd->initSlots) {
			newshift++;
			newslots >>= 1;
		}
		/* Try to allocate new table. Be ready to back off. */
		saveHandler = MMoutOfMemory;
		MMoutOfMemory = dd->outOfMemCallback;
		newlist = ALLOC(DdNodePtr, newslots);
		MMoutOfMemory = saveHandler;
		if (newlist == NULL) {
			(void) fprintf(dd->err, "changeExpnStoPD: create subtable lack of memory\n");
			return(0);
		} else {
			dd->slots += ((int) newslots - slots);
			dd->minDead = (unsigned)
			(dd->gcFrac * (double) dd->slots);
			dd->cacheSlack = (int)
			ddMin(dd->maxCacheHard, DD_MAX_CACHE_TO_SLOTS_RATIO
			* dd->slots) - 2 * (int) dd->cacheSlots;
			dd->memused +=
			((int) newslots - slots) * sizeof(DdNodePtr);
			FREE(list);
			slots =  newslots;
			shift = newshift;
			list = newlist;

			dd->subtables[level].nodelist = list;
			dd->subtables[level].slots = slots;
			dd->subtables[level].shift = shift;
			dd->subtables[level].maxKeys = slots * DD_MAX_SUBTABLE_DENSITY;
		}
	}
	/* Initialize new subtable. */
	for (i = 0; i < slots; i++) {
		list[i] = sentinel;
	}
	/* Replace successors of nodes in the given level. */
	while (nodechain != NULL) {
		next = nodechain->next;
		f_l = cuddT(nodechain);
		f_h = cuddE(nodechain);
		assert(f_l != f_h);
		/* f_newl = f_h, f_newh = f_l XOR f_h */
		f_newh = BkfddXorRecur_Inner(dd, f_l, f_h);
		if (f_newh == NULL) {
			/* Compute new high successor failed, out of memory. */
			(void) fprintf(dd->err, "changeExpnStoPD: compute new high lack of memory\n");
			return(0);
		}
		cuddRef(f_newh);
		cuddDeref(f_l);
		/* f_newl may complemented. */
		cuddT(nodechain) = f_h;
		cuddE(nodechain) = f_newh;
		assert(f_newh != zero);
		/* Re-compute hash value, and re-insert to subtable. */
		posn = ddHash(f_h, f_newh, shift);
		previousP = &(list[posn]);
		tmp = *previousP;
		while (f_h < cuddT(tmp)) {
			previousP = &(tmp->next);
			tmp = *previousP;
		}
		while (f_h == cuddT(tmp) && f_newh < cuddE(tmp)) {
			previousP = &(tmp->next);
			tmp = *previousP;
		}
		nodechain->next = *previousP;
		*previousP = nodechain;
		nodechain = next;
	}

	if (dec == CS) 				{ dd->expansion[level] = CPD; }
	else if (dec == BS) 	{ dd->expansion[level] = BPD; }

	/* clear cache, gc and recounting isolated projection functions */
	changeExpnPostProcess(dd,level+1);

	/* Recover dynamic reordering setting. */
	dd->autoDyn = reorderSave;
	dd->gcEnabled = gcSave;

	return(1);
}	/* end of changeExpnStoPD */


/**
	@brief Change expansion types, between classical expansions
	and their corresponding biconditional expansions at internal level.
	Not at bottom. 
	Expansion types at bottom level has no effect on DD size.
	
	@detials If the given level corresponds to classical expansion,
	change to its corresponding biconditional expansion.
	If the given level corresponds to biconditional expansion,
	change to its corresponding classical expansion.

	1. Disable auto reordering and garbage collecting.
	2. Create new subtable if needed.
	3. For all nodes of given level, use ITE to generate new successors.
	4. Modify successors of nodes.
	5. Update hash value of nodes.
	6. Re-insert nodes to new subtable.
	7. Collecting garbages.
	8. Recover auto reordering setting.

	@return 1 if success, otherwise fail. After changing, we need to do GC.
	
 	This procedure won't violate "low-uncomplemented" principle.

	@NOTE Assume x,y are adjacent variable.
	CS => BS:	
		F_newl = F_x=y = y*F_x=1 + !y*F_x=0 = ITE(y,F_x=1,F_x=0) = ITE(y,F_oldl,F_oldh);
		F_newh = F_x!=y = y*F_x=0 + !y*F_x=1 = ITE(y,F_x=0,F_x=1) = ITE(y,F_oldh,F_oldl);

	BS => CS:
		F_newl = F_x=1 = y*F_x=y + !y*F_x!=y = ITE(y,F_oldl,F_oldh) 
		F_newh = F_x=0 = y*F_x!=y + !y*F_x=y = ITE(y,F_oldh,F_oldl);

	CND => BND:
		F_newl = F_x=y = y*F_x=1 + !y*F_x=0 = ITE(y,F_x=1,F_x=0)
					 		= F_x=1 xor !y*(F_x=1 xor F_x=0) = F_oldl xor !y*F_oldh;
		F_newh = F_oldh;

	BND => CND:
		F_newl = F_x=1 = F_x=y xor !y*(F_x=y xor F_x!=y) = F_oldl xor !y*F_oldh;
		F_newh = F_oldh;

	CPD => BPD:
		F_newl = F_x!=y = y*F_x=0 + !y*F_x=1 = F_x=0 xor !y*(F_x=1 xor F_x=0)
							= F_oldl xor !y*F_oldh;
		F_newh = F_oldh;

	By CUDD's standard triples, since F_oldl always regular,
	F_newl are always regular.
	
*/
int
changeExpnBetweenBiCla(
	DdManager * dd,
	int level)
{	
	assert(level != (dd->size-1));
	assert(dd->dead == 0);

	/* Disable auto reordering and garbage collecting. */
	int reorderSave = dd->autoDyn;
	dd->autoDyn = 0;
	int gcSave = dd->gcEnabled;
	dd->gcEnabled = 0;
	/* Move all nodes to a chain, create new table if needed,
	otherwise use old table. */
	DdNode *nodechain, *p, *next, *f_newl, *f_newh, *tmp, *f_h_tmp, *f_l, *f_h;
	nodechain = p = next = f_newl = f_newh = tmp = f_h_tmp = f_l = f_h = NULL;
	DdNodePtr *previousP = NULL;
	unsigned int i, posn;
	extern DD_OOMFP MMoutOfMemory;
	DD_OOMFP saveHandler;

	DdNodePtr *list = dd->subtables[level].nodelist;
	int oldkeys = dd->subtables[level].keys;
	unsigned int slots = dd->subtables[level].slots;
	int shift = dd->subtables[level].shift;
	DdNode *sentinel = &(dd->sentinel);
	int dec = dd->expansion[level];

	/* Empty current nodelist, put them to nodechain. */
	for (i = 0; i < slots; i++) {
		p = list[i];
		while (p != sentinel) {
			next = p->next;
			p->next = nodechain;
			nodechain = p;
			p = next;
		} /* while there are elements in the collision chain */
	} /* for each slot of the subtable */
	DdNode *zero = Cudd_Not(DD_ONE(dd));
	if (((unsigned) oldkeys >= slots || (unsigned) slots == dd->initSlots) &&
	(unsigned) oldkeys <= DD_MAX_SUBTABLE_DENSITY * slots) {
	/* Use old table. Do nothing. */
	} else {
	/* Create new table. The number of keys unchanged. */
		DdNodePtr *newlist;
		unsigned int newslots = slots;
		int newshift = shift;
		while ((unsigned) oldkeys > DD_MAX_SUBTABLE_DENSITY * newslots) {
			newshift--;
			newslots <<= 1;
		}
		while ((unsigned) oldkeys < newslots &&
		newslots > dd->initSlots) {
			newshift++;
			newslots >>= 1;
		}
		/* Try to allocate new table. Be ready to back off. */
		saveHandler = MMoutOfMemory;
		MMoutOfMemory = dd->outOfMemCallback;
		newlist = ALLOC(DdNodePtr, newslots);
		MMoutOfMemory = saveHandler;
		if (newlist == NULL) {
			(void) fprintf(dd->err, "changeExpnBetweenBiCla: create subtable lack of memory\n");
			return(0);
		} else {
			dd->slots += ((int) newslots - slots);
			dd->minDead = (unsigned)
			(dd->gcFrac * (double) dd->slots);
			dd->cacheSlack = (int)
			ddMin(dd->maxCacheHard, DD_MAX_CACHE_TO_SLOTS_RATIO
			* dd->slots) - 2 * (int) dd->cacheSlots;
			dd->memused +=
			((int) newslots - slots) * sizeof(DdNodePtr);
			FREE(list);
			slots =  newslots;
			shift = newshift;
			list = newlist;

			dd->subtables[level].nodelist = list;
			dd->subtables[level].slots = slots;
			dd->subtables[level].shift = shift;
			dd->subtables[level].maxKeys = slots * DD_MAX_SUBTABLE_DENSITY;
		}
	}
	/* Initialize new(old) subtable. */
	for (i = 0; i < slots; i++) {
		list[i] = sentinel;
	}
	/* Get variable for computing newlow, newhigh. 
		level+1 should be safe. */
	DdNode *y_var = dd->vars[dd->invperm[level+1]];
	cuddRef(y_var);
	if (y_var == NULL) { return(0); }
	if (isShan(dec)) {
		/* Replace successors of nodes in the given level. */
		while (nodechain != NULL) {
			next = nodechain->next;
			f_l = cuddT(nodechain);
			f_h = cuddE(nodechain);
			assert(f_l != f_h);
			f_newl = BkfddIteRecur_Inner(dd, y_var, f_l, f_h);
			if (f_newl == NULL) {
				/* Compute new low successor failed, out of memory. */
				(void) fprintf(dd->err, "changeExpnBetweenBiCla: compute new low lack of memory\n");
				return(0);
			}
			cuddRef(f_newl);
			
			f_newh = BkfddIteRecur_Inner(dd, y_var, f_h, f_l);
			if (f_newh == NULL) {
				Cudd_IterDerefBdd(dd,f_newl);
				/* Compute new high successor failed, out of memory. */
				(void) fprintf(dd->err, "changeExpnBetweenBiCla: compute new high lack of memory\n");
				return(0);
			}
			cuddRef(f_newh);
			assert(f_newl != f_newh);
			/* Deref old low and old high. */
			cuddDeref(f_l);
			cuddDeref(f_h);
			cuddT(nodechain) = f_newl;
			cuddE(nodechain) = f_newh;

			/* Re-compute hash value, and re-insert to subtable. */
			posn = ddHash(f_newl, f_newh, shift);
			previousP = &(list[posn]);
			tmp = *previousP;
			while (f_newl < cuddT(tmp)) {
				previousP = &(tmp->next);
				tmp = *previousP;
			}
			while (f_newl == cuddT(tmp) && f_newh < cuddE(tmp)) {
				previousP = &(tmp->next);
				tmp = *previousP;
			}
			nodechain->next = *previousP;
			*previousP = nodechain;
			nodechain = next;
		}
	} else { // Davio expansion
		/* Replace successors of nodes in the given level. */
		while (nodechain != NULL) {
			next = nodechain->next;
			f_l = cuddT(nodechain);
			f_h = cuddE(nodechain);
			assert(f_h != zero);
			f_h_tmp = BkfddAndRecur_Inner(dd, Cudd_Not(y_var), f_h);
			if (f_h_tmp == NULL) {
				(void) fprintf(dd->err, "changeExpnBetweenBiCla: compute xor lack of memory\n");
				return(0);
			}
			cuddRef(f_h_tmp);

			f_newl = BkfddXorRecur_Inner(dd, f_l, f_h_tmp);
			if (f_newl == NULL) {
				Cudd_IterDerefBdd(dd, f_h_tmp);
				/* Compute new low successor failed, out of memory. */
				(void) fprintf(dd->err, "changeExpnBetweenBiCla: compute new low lack of memory\n");
				return(0);
			}
			cuddRef(f_newl);
			/* Deref old low. */
			cuddDeref(f_l);
			cuddDeref(f_h_tmp);
			cuddT(nodechain) = f_newl;
			/* Re-compute hash value, and re-insert to subtable. */
			posn = ddHash(f_newl, f_h, shift);
			previousP = &(list[posn]);
			tmp = *previousP;
			while (f_newl < cuddT(tmp)) {
				previousP = &(tmp->next);
				tmp = *previousP;
			}
			while (f_newl == cuddT(tmp) && f_h < cuddE(tmp)) {
				previousP = &(tmp->next);
				tmp = *previousP;
			}
			nodechain->next = *previousP;
			*previousP = nodechain;
			nodechain = next;
		}
	}
	cuddDeref(y_var);

	if(dec == CS) 				{	dd->expansion[level] = BS; }
	else if (dec == BS) 	{ dd->expansion[level] = CS; }
	else if (dec == CND)	{ dd->expansion[level] = BND; }
	else if (dec == BND)	{ dd->expansion[level] = CND; }
	else if (dec == CPD)	{ dd->expansion[level] = BPD; }
	else 									{ dd->expansion[level] = CPD; }

	/* clear cache, gc and recounting isolated projection functions */
	changeExpnPostProcess(dd,level+1);

	/* Recover dynamic reordering and garbage collection setting. */
	dd->autoDyn = reorderSave;
	dd->gcEnabled = gcSave;

	return(1);
}	/* end of changeExpnBetweenBiCla */


/** 
	@brief Post process after expansion change.

	@detail Clear cache, do garbage collection for nodes at and bellow
	level, and recount isolated projection functions.

*/
static void
changeExpnPostProcess(
	DdManager * dd,
	int level)
{
	int i;
	unsigned int k, slots;
	DdNode *p, *next;
	p = next = NULL;
	DdNodePtr *previousP = NULL;
	DdNode *sentinel = &(dd->sentinel);

	/* Clean cache. */
	cuddCacheFlush(dd);
	cuddLocalCacheClearAll(dd);
	
	/* GC subtable below current level, there is no dead nodes. */
	for (i = level; i < dd->size; i++) {
		DdNodePtr *nodelist = dd->subtables[i].nodelist;
		slots = dd->subtables[i].slots;
		for (k = 0; k < slots; k ++) {
			previousP = &(nodelist[k]);
			p = *previousP;
			while (p != sentinel) {
				next = p->next;
				if (p->ref == 0) {
					cuddDeref(cuddT(p));
					cuddDeref(cuddE(p));
					cuddDeallocNode(dd,p);
					dd->subtables[i].keys--;
					dd->keys --;
				} else {
					*previousP = p;
					previousP = &(p->next);
				}
				p = next;
			}
			*previousP = sentinel;
		}
	}

	/* Re-count isolated variables. 
		Counter of isolated projection functions
		become invalid during computaion. */
	dd->isolated = 0;
	for (i = 0; i < dd->size; i ++) {
		p = Cudd_Regular(dd->vars[i]);
		if (p->ref == 1) {
			dd->isolated ++;
		}
	}

	return;
} /* end of changeExpnPostProcess */
