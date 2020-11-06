#include<stdint.h>

#define N_LAS 4000000
#define N_PAS 6000000
#define N_DIFF 4000000
uint64_t las[N_DIFF];
uint64_t pas[N_DIFF];
uint64_t l2p_ram[N_LAS];
uint64_t l2p_flash[N_LAS];
uint64_t p;

void write(uint64_t la, uint64_t pa)
{
	if (la >= N_LAS || pa >= N_PAS)
		return;
	/* Update in-ram l2p */
	l2p_ram[la] = pa;
	/* Update in-flash l2p */
	las[p] = la;
	pas[p] = pa;
	p = p + 1;
	if (p == N_DIFF) {
		p = 0;
		for (uint64_t i = 0; i < N_LAS; i++)
			l2p_flash[i] = l2p_ram[i];
	}
}
