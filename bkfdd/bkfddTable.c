/**
  @file

  @ingroup bkfdd

  @brief Functions for inner unique table management.

  @author Xuanxiang Huang

  @copyright
  Copyright (c) 2019-, Jinan University, Guangzhou, China.

  All rights reserved.

======================================================================
	All functions are originate from cuddTable.c.

	@Modification and Extension details
		1. Add special version of unique table find-or-add function.

	2020/5/4: disable cuddLocalCacheClearAll
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

/**
  @brief Checks the unique table for the existence of an internal node.

  @detail A special version which won't trigger garbageCollections
	and dynamic reordering. It use cuddDynamicAllocNode.

	@see cuddUniqueInter	

*/
DdNode *
cuddUniqueInter_Inner(
  DdManager * unique,
  int index,
  DdNode * T,
  DdNode * E)
{
	int pos;
	unsigned int level;
	DdNodePtr *nodelist;
	DdNode *looking;
	DdNodePtr *previousP;
	DdSubtable *subtable;

#ifdef DD_UNIQUE_PROFILE
	unique->uniqueLookUps++;
#endif

	level = unique->perm[index];
	subtable = &(unique->subtables[level]);

#ifdef DD_DEBUG
	assert(level < (unsigned) cuddI(unique,T->index));
	assert(level < (unsigned) cuddI(unique,Cudd_Regular(E)->index));
#endif

	pos = ddHash(T, E, subtable->shift);
	nodelist = subtable->nodelist;
	previousP = &(nodelist[pos]);
	looking = *previousP;

	while (T < cuddT(looking)) {
		previousP = &(looking->next);
		looking = *previousP;
#ifdef DD_UNIQUE_PROFILE
		unique->uniqueLinks++;
#endif
	}
	while (T == cuddT(looking) && E < cuddE(looking)) {
		previousP = &(looking->next);
		looking = *previousP;
#ifdef DD_UNIQUE_PROFILE
		unique->uniqueLinks++;
#endif
	}
	if (T == cuddT(looking) && E == cuddE(looking)) {
		assert((int)(T->ref) > 0);
		assert((int)(Cudd_Regular(E)->ref) > 0);
		assert((int)(looking->ref) >= 0);
		return(looking);
	}

	looking = cuddDynamicAllocNode(unique);
	if (looking == NULL) {
		return(NULL);
	}
	unique->keys++;
	subtable->keys++;

	looking->index = index;
	cuddT(looking) = T;
	cuddE(looking) = E;
	looking->next = *previousP;
	*previousP = looking;
	cuddSatInc(T->ref);		/* we know T is a regular pointer */
	cuddRef(E);

#ifdef DD_DEBUG
	cuddCheckCollisionOrdering(unique,level,pos);
#endif

	return(looking);

} /* end of cuddUniqueInter_Inner */


/** 
	@brief simple garbage collection

	@detail Clear cache, do garbage collection for nodes at and bellow
	level, and recount isolated projection functions.

*/
void
garbageCollectSimple(
	DdManager * unique,
	int level)
{
	int i,k;
  int slots;
	DdNodePtr *previousP = NULL;
	DdNode *tmp, *ff, *next;
  DdNode *sentinel = &(unique->sentinel);

	cuddCacheFlush(unique);

	for (i = level; (int)i < unique->size; i++) {
		DdNodePtr *nodelist = unique->subtables[i].nodelist;
		slots = unique->subtables[i].slots;
		for (k = 0; k < slots; k ++) {
			previousP = &(nodelist[k]);
			ff = *previousP;
			while (ff != sentinel) {
				next = ff->next;
				if (ff->ref == 0) {
					tmp = cuddT(ff);
					cuddSatDec(tmp->ref);
					tmp = Cudd_Regular(cuddE(ff));
					cuddSatDec(tmp->ref);
					cuddDeallocNode(unique,ff);
					unique->subtables[i].keys--;
					unique->keys --;
				} else {
					*previousP = ff;
					previousP = &(ff->next);
				}
				ff = next;
			}
			*previousP = sentinel;
		}
		unique->subtables[i].dead = 0;
	}
	if (level == 0) {
		unique->dead = 0;
	}

	return;
} /* end of garbageCollectSimple */
