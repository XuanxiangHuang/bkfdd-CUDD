/**
  @file

  @ingroup bkfdd

  @brief Choose Better expansions for each level of BKFDDs.

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
#include "bkfdd_bnet.h"

static void choosePreProcess(DdManager * table,	int level);
//static int getGroupSize(DdManager * table, int level);
//static int getMaxGroupSize(DdManager * table);
//static int checkCombineGroup(DdManager * table, int i);


/**
	@biref Restrict version of chooseSD3
*/
int
chooseSD3_restricted_bnet(
	DdManager * table,
	BnetNetwork * network)
{
	choosePreProcess(table,0);

	int interactNull;
	if (table->interact == NULL) {
		int res = cuddInitInteract(table);
		if (res == 0) return(0);
		interactNull = 1;
	} else {
		interactNull = 0;
	}

	int ii;

	unsigned int oldKeysTotal, newKeysTotal, initKeysTotal;
	unsigned int newKeysTotal1, newKeysTotal2;
	int initExpn, expn1, expn2, expn;
	initKeysTotal = oldKeysTotal = table->keys-table->isolated;
	/* some arguments */
	// number of davio expansions allowed to exist
	int davio_exist_bound = (int)(table->size * table->davio_exist_factor);
	// how many times we allowed to fail in choosing better expansions
	int failedBound = (int)(davio_exist_bound * table->choose_fail_bound_factor);
	// how many times we have failed.
	int failedCount = 0;
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

	unsigned long startTime = util_cpu_time();

	for (ii = 0; ii < table->size-1; ii += 1) {
		assert(nonShan <= upper_bound);
		if (table->subtables[ii].keys == 0) { continue; }
		if ( (nonShan == upper_bound) &&
				isShan(table->expansion[ii]) ) {
			continue;
		} else {
			/*
				1. nonShan == upper_bound and !isShan
				2. nonShan < upper_bound	and isShan
				3. nonShan < upper_bound  and !isShan
			*/
			initExpn = table->expansion[ii];

			if (isShan(table->expansion[ii])) {
				// CS->CND->CPD or BS->BND->BPD
				if (!changeExpnBetweenSND_bnet(table,ii,network)) {
					printf("chooseSD3: %d, choose better expn failed\n", ii);
					goto failed;
				}
				newKeysTotal1 = table->keys-table->isolated;
				expn1 = table->expansion[ii];
				if (!changeExpnBetweenNDPD_bnet(table,ii,network)) {
					printf("chooseSD3: %d, choose better expn failed\n", ii);
					goto failed;
				}
				newKeysTotal2 = table->keys-table->isolated;
				expn2 = table->expansion[ii];
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
					if (!changeExpnPDtoS_bnet(table,ii,network)) {
						printf("chooseSD3: %d, choose better expn failed\n", ii);
						goto failed;
					}
					assert((table->keys-table->isolated) == oldKeysTotal);
					failedCount ++;
				} else {
					oldKeysTotal = newKeysTotal;
					if (newKeysTotal == newKeysTotal1) {
						if (!changeExpnBetweenNDPD_bnet(table,ii,network)) {
							printf("chooseSD3: %d, choose better expn failed\n", ii);
							goto failed;
						}
						assert((table->keys-table->isolated) == newKeysTotal1);
					}
				}
			} else if (isNDavio(table->expansion[ii])) {
				// CND->CPD->CS or BND->BPD->BS
				if (!changeExpnBetweenNDPD_bnet(table,ii,network)) {
					printf("chooseSD3: %d, choose better expn failed\n", ii);
					goto failed;
				}
				newKeysTotal1 = table->keys-table->isolated;
				expn1 = table->expansion[ii];
				if (!changeExpnPDtoS_bnet(table,ii,network)) {
					printf("chooseSD3: %d, choose better expn failed\n", ii);
					goto failed;
				}
				newKeysTotal2 = table->keys-table->isolated;
				expn2 = table->expansion[ii];
				newKeysTotal = ddMin(newKeysTotal1, newKeysTotal2);
				if (newKeysTotal == newKeysTotal1) {
					expn = expn1;
				} else {
					expn = expn2;
				}
//				double key = newKeysTotal;
//				double keyNew = oldKeysTotal * table->choose_new_bound_factor;
//				double keyDav = oldKeysTotal * table->choose_dav_bound_factor;
				int key = newKeysTotal;
				int keyNew = ceil(oldKeysTotal * table->choose_new_bound_factor);
				int keyDav = ceil(oldKeysTotal * table->choose_dav_bound_factor);
				if ( (key >= keyNew) ||
						(!isShan(expn) && (key >= keyDav)) ) {
					if (!changeExpnBetweenSND_bnet(table,ii,network)) {
						printf("chooseSD3: %d, choose better expn failed\n", ii);
						goto failed;					
					}
					assert((table->keys-table->isolated) == oldKeysTotal);
					failedCount ++;
				} else {
					oldKeysTotal = newKeysTotal;
					if (newKeysTotal == newKeysTotal1) {
						if (!changeExpnStoPD_bnet(table,ii,network)) {
							printf("chooseSD3: %d, choose better expn failed\n", ii);
							goto failed;					
						}
						assert((table->keys-table->isolated) == newKeysTotal1);
					}
				}
			} else { // positive Davio
				// CPD->CS->CND or BPD->BS->BND
				if (!changeExpnPDtoS_bnet(table,ii,network)) {
					printf("chooseSD3: %d, choose better expn failed\n", ii);
					goto failed;
				}
				newKeysTotal1 = table->keys-table->isolated;
				expn1 = table->expansion[ii];
				if (!changeExpnBetweenSND_bnet(table,ii,network)) {
					printf("chooseSD3: %d, choose better expn failed\n", ii);
					goto failed;
				}
				newKeysTotal2 = table->keys-table->isolated;
				expn2 = table->expansion[ii];
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
					if (!changeExpnBetweenNDPD_bnet(table,ii,network)) {
						printf("chooseSD3: %d, choose better expn failed\n", ii);
						goto failed;					
					}
					assert((table->keys-table->isolated) == oldKeysTotal);
					failedCount ++;
				} else {
					oldKeysTotal = newKeysTotal;
					if (newKeysTotal == newKeysTotal1) {
						if (!changeExpnBetweenSND_bnet(table,ii,network)) {
							printf("chooseSD3: %d, choose better expn failed\n", ii);
							goto failed;					
						}
						assert((table->keys-table->isolated) == newKeysTotal1);
					}
				}
			}
			// re-count nonShan
			if (isShan(initExpn) && !isShan(table->expansion[ii])) {
				nonShan ++;
			} else if (!isShan(initExpn) && isShan(table->expansion[ii])){
				nonShan --;
			}
			assert(nonShan <= upper_bound);
		}
		if (failedCount == failedBound) { // failed enough times
			break;
		}

		int keyFinal = oldKeysTotal;
		int keyBound = ceil(initKeysTotal * table->choose_lower_bound_factor);
		if (keyFinal <= keyBound) { // has reduced enough nodes
			break;
		}
	}

	int CScount,BScount,CNDcount,BNDcount,CPDcount,BPDcount;
	BScount = CNDcount = BNDcount = CPDcount = BPDcount = 0;
	/* expansion type of bottom variable has no effect on DD size,
		so we assume the bottom variable associate with CS. */
	CScount = 1;
	for (ii = 0; ii < table->size-1; ii ++) {
		switch(table->expansion[ii]) {
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
	printf("CS:%d, BS:%d, CND:%d, BND:%d, CPD:%d, BPD:%d, ",
	CScount,BScount,CNDcount,BNDcount,CPDcount,BPDcount);
	// minus plusinfinity, minusinfinity and zero.
	printf("size from %d to %d in %4g sec }\n",
	initKeysTotal-3, table->keys-table->isolated-3, (double)(util_cpu_time() - startTime)/1000.0);
	
	if (interactNull) {
		FREE(table->interact);
	}
	return(1);

failed:

	fprintf(table->err, "chooseSD3_restricted failed\n");

	if (interactNull) {
		FREE(table->interact);
	}
	return(0);

} /* end of chooseSD3_restricted_bnet */


/**
	@brief Restrict version of chooseSD6
*/
int
chooseSD6_restricted_bnet(
	DdManager * table,
	BnetNetwork * network)
{
	choosePreProcess(table,0);

	int interactNull;
	if (table->interact == NULL) {
		int res = cuddInitInteract(table);
		if (res == 0) return(0);
		interactNull = 1;
	} else {
		interactNull = 0;
	}

	int ii;

	unsigned int oldKeysTotal, newKeysTotal, initKeysTotal;
	unsigned int newKeysTotal1, newKeysTotal2, newKeysTotal3, newKeysTotal4, newKeysTotal5;
	int initExpn, expn1, expn2, expn3, expn4, expn5, expn;
	initKeysTotal = oldKeysTotal = table->keys-table->isolated;
	/* some arguments */
	// number of davio expansions allowed to exist
	int davio_exist_bound = (int)(table->size * table->davio_exist_factor);
	// how many times we allowed to fail in choosing better expansions
	int failedBound = (int)(davio_exist_bound * table->choose_fail_bound_factor);
	// how many times we have failed.
	int failedCount = 0;
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

	unsigned long startTime = util_cpu_time();

	for (ii = 0; ii < table->size-1; ii += 1) {
		assert(nonShan <= upper_bound);
		if (table->subtables[ii].keys == 0) { continue; }
		if (cuddTestInteract(table,table->invperm[ii],table->invperm[ii+1])) {
			if ( (nonShan == upper_bound) &&
					isShan(table->expansion[ii]) ) {
				/* If number of nonShan expansion reach upper bound
				and current level associated with Shan, then try BS or CS. */
				if (!changeExpnBetweenBiCla_bnet(table,ii,network)) {
					printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
					goto failed;
				}
				newKeysTotal = table->keys-table->isolated;

				int key = newKeysTotal;
				int keyNew = ceil(oldKeysTotal * table->choose_new_bound_factor);
				if ( key >= keyNew ) {
					if (!changeExpnBetweenBiCla_bnet(table,ii,network)) {
						printf("chooseSD6_restricted: %d, roll back failed\n", ii);
						goto failed;
					}
					newKeysTotal = table->keys-table->isolated;
					assert(newKeysTotal == oldKeysTotal);
					failedCount ++;
				} else {
					oldKeysTotal = newKeysTotal;
				}
			} else {
				/*
					1. nonShan == upper_bound and !isShan
					2. nonShan < upper_bound	and isShan
					3. nonShan < upper_bound  and !isShan
				*/
				initExpn = table->expansion[ii];
/* 
	CS->CPD->CND->BND->BPD->BS->CS or CND->CPD->CS->BS->BPD->BND->CND or CPD->CND->CS->BS->BND->BPD->CPD
	BS->BPD->BND->CND->CPD->CS->BS or BND->BPD->BS->CS->CPD->CND->BND or BPD->BND->BS->CS->CND->CPD->BPD
*/ 
				if (isShan(table->expansion[ii])) {
					// CS->CPD or BS->BPD
					if (!changeExpnStoPD_bnet(table,ii,network)) {
						printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
						goto failed;
					}
					newKeysTotal1 = table->keys-table->isolated;
					expn1 = table->expansion[ii];
					// CPD->CND or BPD->BND
					if (!changeExpnBetweenNDPD_bnet(table,ii,network)) {
						printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
						goto failed;
					}
					newKeysTotal2 = table->keys-table->isolated;
					expn2 = table->expansion[ii];
					// CND->BND or BND->CND
					if (!changeExpnBetweenBiCla_bnet(table,ii,network)) {
						printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
						goto failed;
					}
					newKeysTotal3 = table->keys-table->isolated;
					expn3 = table->expansion[ii];
					// BND->BPD or CND->CPD
					if (!changeExpnBetweenNDPD_bnet(table,ii,network)) {
						printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
						goto failed;
					}
					newKeysTotal4 = table->keys-table->isolated;
					expn4 = table->expansion[ii];
					// BPD->BS or CPD->CS
					if (!changeExpnPDtoS_bnet(table,ii,network)) {
						printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
						goto failed;
					}
					assert(isShan(table->expansion[ii]));
					newKeysTotal5 = table->keys-table->isolated;
					expn5 = table->expansion[ii];
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
						if (!changeExpnBetweenBiCla_bnet(table,ii,network)) {
							printf("chooseSD6_restricted: %d, roll back failed\n", ii);
							goto failed;
						}
						assert((table->keys-table->isolated) == oldKeysTotal);
						failedCount ++;
					} else {
						if (newKeysTotal == newKeysTotal1) {
							if (!changeExpnBetweenBiCla_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, roll back failed\n", ii);
								goto failed;
							}
							assert((table->keys-table->isolated) == oldKeysTotal);
							if (!changeExpnStoPD_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, roll back failed\n", ii);
								goto failed;
							}
							assert((table->keys-table->isolated) == newKeysTotal1);
						} else if (newKeysTotal == newKeysTotal2) {
							if (!changeExpnStoPD_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, roll back failed\n", ii);
								goto failed;
							}
							assert((table->keys-table->isolated) == newKeysTotal4);
							if (!changeExpnBetweenNDPD_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, roll back failed\n", ii);
								goto failed;
							}
							assert((table->keys-table->isolated) == newKeysTotal3);
							if (!changeExpnBetweenBiCla_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, roll back failed\n", ii);
								goto failed;
							}
							assert((table->keys-table->isolated) == newKeysTotal2);
						} else if (newKeysTotal == newKeysTotal3) {
							if (!changeExpnStoPD_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, roll back failed\n", ii);
								goto failed;
							}
							assert((table->keys-table->isolated) == newKeysTotal4);
							if (!changeExpnBetweenNDPD_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, roll back failed\n", ii);
								goto failed;
							}
							assert((table->keys-table->isolated) == newKeysTotal3);
						} else if (newKeysTotal == newKeysTotal4) {
							if (!changeExpnStoPD_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, roll back failed\n", ii);
								goto failed;
							}
							assert((table->keys-table->isolated) == newKeysTotal4);
						}
						oldKeysTotal = newKeysTotal;
					}
				} else if (isNDavio(table->expansion[ii])) {
					// CND->CPD or BND->BPD
					if (!changeExpnBetweenNDPD_bnet(table,ii,network)) {
						printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
						goto failed;
					}
					newKeysTotal1 = table->keys-table->isolated;
					expn1 = table->expansion[ii];
					// CPD->CS or BPD->BS
					if (!changeExpnPDtoS_bnet(table,ii,network)) {
						printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
						goto failed;
					}
					newKeysTotal2 = table->keys-table->isolated;
					expn2 = table->expansion[ii];
					// CS->BS or BS->CS
					if (!changeExpnBetweenBiCla_bnet(table,ii,network)) {
						printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
						goto failed;
					}
					newKeysTotal3 = table->keys-table->isolated;
					expn3 = table->expansion[ii];
					// BS->BPD or CS->CPD
					if (!changeExpnStoPD_bnet(table,ii,network)) {
						printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
						goto failed;
					}
					newKeysTotal4 = table->keys-table->isolated;
					expn4 = table->expansion[ii];
					// BPD->BND or CPD->CND
					if (!changeExpnBetweenNDPD_bnet(table,ii,network)) {
						printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
						goto failed;
					}
					assert(isNDavio(table->expansion[ii]));
					newKeysTotal5 = table->keys-table->isolated;
					expn5 = table->expansion[ii];
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
						if (!changeExpnBetweenBiCla_bnet(table,ii,network)) {
							printf("chooseSD6_restricted: %d, roll back failed\n", ii);
							goto failed;
						}
						assert((table->keys-table->isolated) == oldKeysTotal);
						failedCount ++;
					} else {
						if (newKeysTotal == newKeysTotal1) {
							if (!changeExpnBetweenBiCla_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, roll back failed\n", ii);
								goto failed;
							}
							assert((table->keys-table->isolated) == oldKeysTotal);
							if (!changeExpnBetweenNDPD_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, roll back failed\n", ii);
								goto failed;
							}
							assert((table->keys-table->isolated) == newKeysTotal1);
						} else if (newKeysTotal == newKeysTotal2) {
							if (!changeExpnBetweenNDPD_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, roll back failed\n", ii);
								goto failed;
							}
							assert((table->keys-table->isolated) == newKeysTotal4);
							if (!changeExpnPDtoS_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, roll back failed\n", ii);
								goto failed;
							}
							assert((table->keys-table->isolated) == newKeysTotal3);
							if (!changeExpnBetweenBiCla_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, roll back failed\n", ii);
								goto failed;
							}
							assert((table->keys-table->isolated) == newKeysTotal2);
						} else if (newKeysTotal == newKeysTotal3) {
							if (!changeExpnBetweenNDPD_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, roll back failed\n", ii);
								goto failed;
							}
							assert((table->keys-table->isolated) == newKeysTotal4);
							if (!changeExpnPDtoS_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, roll back failed\n", ii);
								goto failed;
							}
							assert((table->keys-table->isolated) == newKeysTotal3);
						} else if (newKeysTotal == newKeysTotal4) {
							if (!changeExpnBetweenNDPD_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, roll back failed\n", ii);
								goto failed;
							}
							assert((table->keys-table->isolated) == newKeysTotal4);
						}
						oldKeysTotal = newKeysTotal;
					}
				} else { // positive Davio
					// CPD->CND->CS->BS->BND->BPD->CPD or BPD->BND->BS->CS->CND->CPD->BPD
					// CPD->CND or BPD->BND
					if (!changeExpnBetweenNDPD_bnet(table,ii,network)) {
						printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
						goto failed;
					}
					newKeysTotal1 = table->keys-table->isolated;
					expn1 = table->expansion[ii];
					// CND->CS or BND->BS
					if (!changeExpnBetweenSND_bnet(table,ii,network)) {
						printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
						goto failed;
					}
					newKeysTotal2 = table->keys-table->isolated;
					expn2 = table->expansion[ii];
					// CS->BS or BS->CS
					if (!changeExpnBetweenBiCla_bnet(table,ii,network)) {
						printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
						goto failed;
					}
					newKeysTotal3 = table->keys-table->isolated;
					expn3 = table->expansion[ii];
					// BS->BND or CS->CND
					if (!changeExpnBetweenSND_bnet(table,ii,network)) {
						printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
						goto failed;
					}
					newKeysTotal4 = table->keys-table->isolated;
					expn4 = table->expansion[ii];
					// BND->BPD or CND->CPD
					if (!changeExpnBetweenNDPD_bnet(table,ii,network)) {
						printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
						goto failed;
					}
					assert(isPDavio(table->expansion[ii]));
					newKeysTotal5 = table->keys-table->isolated;
					expn5 = table->expansion[ii];
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
						if (!changeExpnBetweenBiCla_bnet(table,ii,network)) {
							printf("chooseSD6_restricted: %d, roll back failed\n", ii);
							goto failed;
						}
						assert((table->keys-table->isolated) == oldKeysTotal);
						failedCount ++;
					} else {
						if (newKeysTotal == newKeysTotal1) {
							if (!changeExpnBetweenBiCla_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, roll back failed\n", ii);
								goto failed;
							}
							assert((table->keys-table->isolated) == oldKeysTotal);
							if (!changeExpnBetweenNDPD_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, roll back failed\n", ii);
								goto failed;
							}
							assert((table->keys-table->isolated) == newKeysTotal1);
						} else if (newKeysTotal == newKeysTotal2) {
							if (!changeExpnBetweenNDPD_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, roll back failed\n", ii);
								goto failed;
							}
							assert((table->keys-table->isolated) == newKeysTotal4);
							if (!changeExpnBetweenSND_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, roll back failed\n", ii);
								goto failed;
							}
							assert((table->keys-table->isolated) == newKeysTotal3);
							if (!changeExpnBetweenBiCla_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, roll back failed\n", ii);
								goto failed;
							}
							assert((table->keys-table->isolated) == newKeysTotal2);
						} else if (newKeysTotal == newKeysTotal3) {
							if (!changeExpnBetweenNDPD_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, roll back failed\n", ii);
								goto failed;
							}
							assert((table->keys-table->isolated) == newKeysTotal4);
							if (!changeExpnBetweenSND_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, roll back failed\n", ii);
								goto failed;
							}
							assert((table->keys-table->isolated) == newKeysTotal3);
						} else if (newKeysTotal == newKeysTotal4) {
							if (!changeExpnBetweenNDPD_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, roll back failed\n", ii);
								goto failed;
							}
							assert((table->keys-table->isolated) == newKeysTotal4);
						}
						oldKeysTotal = newKeysTotal;
					}
				}
				// re-count nonShan
				if (isShan(initExpn) && !isShan(table->expansion[ii])) {
					nonShan ++;
				} else if (!isShan(initExpn) && isShan(table->expansion[ii])){
					nonShan --;
				}
				assert(nonShan <= upper_bound);
			}
		} else { // not interact
			if ( (nonShan == upper_bound) &&
					isShan(table->expansion[ii]) ) {
				continue;
			} else {
				/*
					1. nonShan == upper_bound and !isShan
					2. nonShan < upper_bound	and isShan
					3. nonShan < upper_bound  and !isShan
				*/
				initExpn = table->expansion[ii];

				if (isShan(table->expansion[ii])) {
					// CS->CND->CPD or BS->BND->BPD
					if (!changeExpnBetweenSND_bnet(table,ii,network)) {
						printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
						goto failed;
					}
					newKeysTotal1 = table->keys-table->isolated;
					expn1 = table->expansion[ii];
					if (!changeExpnBetweenNDPD_bnet(table,ii,network)) {
						printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
						goto failed;
					}
					newKeysTotal2 = table->keys-table->isolated;
					expn2 = table->expansion[ii];
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
						if (!changeExpnPDtoS_bnet(table,ii,network)) {
							printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
							goto failed;
						}
						assert((table->keys-table->isolated) == oldKeysTotal);
						failedCount ++;
					} else {
						oldKeysTotal = newKeysTotal;
						if (newKeysTotal == newKeysTotal1) {
							if (!changeExpnBetweenNDPD_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
								goto failed;
							}
							assert((table->keys-table->isolated) == newKeysTotal1);
						}
					}
				} else if (isNDavio(table->expansion[ii])) {
					// CND->CPD->CS or BND->BPD->BS
					if (!changeExpnBetweenNDPD_bnet(table,ii,network)) {
						printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
						goto failed;
					}
					newKeysTotal1 = table->keys-table->isolated;
					expn1 = table->expansion[ii];
					if (!changeExpnPDtoS_bnet(table,ii,network)) {
						printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
						goto failed;
					}
					newKeysTotal2 = table->keys-table->isolated;
					expn2 = table->expansion[ii];
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
						if (!changeExpnBetweenSND_bnet(table,ii,network)) {
							printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
							goto failed;					
						}
						assert((table->keys-table->isolated) == oldKeysTotal);
						failedCount ++;
					} else {
						oldKeysTotal = newKeysTotal;
						if (newKeysTotal == newKeysTotal1) {
							if (!changeExpnStoPD_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
								goto failed;					
							}
							assert((table->keys-table->isolated) == newKeysTotal1);
						}
					}
				} else { // positive Davio
					// CPD->CS->CND or BPD->BS->BND
					if (!changeExpnPDtoS_bnet(table,ii,network)) {
						printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
						goto failed;
					}
					newKeysTotal1 = table->keys-table->isolated;
					expn1 = table->expansion[ii];
					if (!changeExpnBetweenSND_bnet(table,ii,network)) {
						printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
						goto failed;
					}
					newKeysTotal2 = table->keys-table->isolated;
					expn2 = table->expansion[ii];
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
						if (!changeExpnBetweenNDPD_bnet(table,ii,network)) {
							printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
							goto failed;					
						}
						assert((table->keys-table->isolated) == oldKeysTotal);
						failedCount ++;
					} else {
						oldKeysTotal = newKeysTotal;
						if (newKeysTotal == newKeysTotal1) {
							if (!changeExpnBetweenSND_bnet(table,ii,network)) {
								printf("chooseSD6_restricted: %d, choose better expn failed\n", ii);
								goto failed;					
							}
							assert((table->keys-table->isolated) == newKeysTotal1);
						}
					}
				}
				// re-count nonShan
				if (isShan(initExpn) && !isShan(table->expansion[ii])) {
					nonShan ++;
				} else if (!isShan(initExpn) && isShan(table->expansion[ii])){
					nonShan --;
				}
				assert(nonShan <= upper_bound);
			}
		}
		if (failedCount == failedBound) { // failed enough times
			break;
		}

		int keyFinal = oldKeysTotal;
		int keyBound = ceil(initKeysTotal * table->choose_lower_bound_factor);
		if (keyFinal <= keyBound) { // has reduced enough nodes
			break;
		}
	}
	
	int CScount,BScount,CNDcount,BNDcount,CPDcount,BPDcount;
	BScount = CNDcount = BNDcount = CPDcount = BPDcount = 0;
	/* expansion type of bottom variable has no effect on DD size,
		so we assume the bottom variable associate with CS. */
	CScount = 1;
	for (ii = 0; ii < table->size-1; ii ++) {
		switch(table->expansion[ii]) {
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
	printf("CS:%d, BS:%d, CND:%d, BND:%d, CPD:%d, BPD:%d, ",
	CScount,BScount,CNDcount,BNDcount,CPDcount,BPDcount);
	// minus plusinfinity, minusinfinity and zero.
	printf("size from %d to %d in %4g sec }\n",
	initKeysTotal-3, table->keys-table->isolated-3, (double)(util_cpu_time() - startTime)/1000.0);
	
	if (interactNull) {
		FREE(table->interact);
	}
	return(1);

failed:

	fprintf(table->err, "chooseSD6_restricted failed\n");

	if (interactNull) {
		FREE(table->interact);
	}
	return(0);

} /* end of chooseSD6_restricted_bnet */


/** 
	@brief Previous process before DD transformation.

	@detail Clear cache, do garbage collection for nodes at and bellow
	level, and recount isolated projection functions.
	Finally check unique table.

*/
static void
choosePreProcess(
	DdManager * table,
	int level)
{
	int i;
	unsigned int k, slots;
	DdNode *p, *next;
	p = next = NULL;
	DdNodePtr *previousP = NULL;
	DdNode *sentinel = &(table->sentinel);

	/* Clean cache. */
	cuddCacheFlush(table);
	
	/* GC subtable below current level, there is no dead nodes. */
	for (i = level; i < table->size; i++) {
		DdNodePtr *nodelist = table->subtables[i].nodelist;
		slots = table->subtables[i].slots;
		for (k = 0; k < slots; k ++) {
			previousP = &(nodelist[k]);
			p = *previousP;
			while (p != sentinel) {
				next = p->next;
				if (p->ref == 0) {
					cuddDeref(cuddT(p));
					cuddDeref(cuddE(p));
					cuddDeallocNode(table,p);
					table->subtables[i].keys--;
					table->keys --;
				} else {
					*previousP = p;
					previousP = &(p->next);
				}
				p = next;
			}
			*previousP = sentinel;
		}
		table->subtables[i].dead = 0;
	}
	if (level == 0) {
		table->dead = 0;
	}

	/* Re-count isolated variables. */
	table->isolated = 0;
	for (i = 0; i < table->size; i ++) {
		p = Cudd_Regular(table->vars[i]);
		if (p->ref == 1) {
			table->isolated ++;
		}
	}

	return;
} /* end of choosePreProcess */

#if 0
/** @brief get size of variable group containing current variable,
	a variable group has the form: B*-B*-...-C*, viz start with 
	a biconditional expansion and end with a classical expansion.
	and the size is the number of variables in it.
	
	@sideeffect None

*/
static int
getGroupSize(
	DdManager * table,
	int level)
{
	int i;
	int group_size = 0;
	for (i = level-1; i >= 0; i --) {
		if (isBi(table->expansion[i])) {
			group_size ++;
		} else { // encouter the end of previous group
			break;
		}
	}
	for (i = level; i <= table->size-1; i ++) {
		if (isBi(table->expansion[i])) {
			group_size ++;
		} else { // reach the end of current group
			group_size ++;
			break;
		}
	}
	return group_size;
} /* End of getGroupSize */


/** 
	@brief Get maximum size of variable group

	@sideeffect None

*/
static int
getMaxGroupSize(
	DdManager * table)
{
	int i;
	int max_group_size, group_size;
	max_group_size = group_size = 0;
	for (i = 0; i <= table->size-1; i ++) {
		if (isBi(table->expansion[i])) {
			group_size ++;
		} else {
			group_size ++;
			if (group_size > max_group_size) {
				max_group_size = group_size;
			}
			group_size = 0;
		}
	}
	return max_group_size;
} /* End of getMaxGroupSize */


/** 
	@brief check whether we can combine two adjacent variables,
	given the maximum size of variable group

	@detail 
	case 1: cla-cla => bi-cla or cla-bi => bi-bi; it may add next group to current group.
			it is not allowed if the resulting group is too large, then return 0;
			otherwise return 1.

	case 2: bi-cla => cla-cla or bi-bi => cla-bi;
			it is always allowed since it may to divide current group,
			so return 1.

	@sideeffect None
*/
static int
checkCombineGroup(
	DdManager * table,
	int i)
{
	if (isBi(table->expansion[i])) return 1;
	
	int group_sizei = getGroupSize(table, i);
	int group_sizei1 = getGroupSize(table, i+1);
	assert(group_sizei <= GROUP_SIZE);
	assert(group_sizei1 <= GROUP_SIZE);
	
	int cla_cla = isCla(table->expansion[i]) && isCla(table->expansion[i+1]);
	int cla_bi = isCla(table->expansion[i]) && isBi(table->expansion[i+1]);
	if ( (cla_cla && (GROUP_SIZE == group_sizei)) ||
		 (cla_bi && ((group_sizei + group_sizei1) > GROUP_SIZE)) ) {
		return 0;
	}
	return 1;
} /* End of checkCombineGroup */
#endif