//============================================================================
// Name        : MAMC.cpp
// Author      : Zhi Lu
// Version     : 18/07/2019
// Copyright   : LERIA, Université d'Angers, France
// Description :
//============================================================================

#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <time.h>
#include <math.h>

#define MAX_INT 1.0E+8
#define MIN(X,Y)  ((X) <= (Y) ? (X) : (Y))

using namespace std;


int n_vtx, n_edg;
double dens;
int **adj_lst;
int *adj_len;

int *f_set, *n_set, *g_set;
long fbest, nbest, gbest;
int **deg_to;
int *cut_set, *cut_pos;
int vol0, vol1, cut;
int s0, vs1, cs;

int iter;
int *ttenure;
int best_add[100000], tabu_add[100000];
int best_len, tabu_len;
long best_sol, tabu_sol;

int TD;        	   			    // parameter, non-improving tabu depth
int alfa;              		    // parameter, tabu tenure management factor
static int PN = 20;             // the size of population

int **pop;
long *fp;
int **p_dis;                    // the distance between two solutions of pop, p_dis[PN+1][PN+1]
int *m_dis;                     // the distance between solution in pop and pop (min distance)
double *score;
int *mom, *dad;
int parent[10];

int run_time;
int run_num;
double ftime, ntime, gtime;
long seed;
double start_time, end_time;

char *instance_name;            // instance file name
char *data_set;                 // data set name
char instance_path[10000];      // instance file path
char MQI_path[10000];           // MQI file path
char statistic_path[10000];     // statistical file path
char result_path[10000];        // result path
char final_result_path[10000];  // final result path


/* function prototype */
void read_graph(char*);
bool verify_size(int*);
void verify_sol(int*, long&);
void verify_final_result(int*, long&);
void cut_set_update(int*, int&);
void initialize(int*, long&);
int is_duplicate(int*, int&);
int distance_two(int&, int&);
int distance_pop(int*, int);
void read_MQI(char*, int&);
void construct_sol();
void initial_pop();
void select_parent();
void double_cutting_point_crossover(int*, int*, long&, long&);
void delta_update_add(int*, int&);
void evaluate_add(int*, int&);
void tabu_search(int*, long&, double&);
void mutation(int*, long&, int&);
void max_distance(int*, long&, int&, int&);
void update_pop(int*, long&);
void Mem_Alg();
void Main_Mem_Alg();
void free_memory();


void read_graph(char *filename)
{
	string line;
	ifstream f1(filename);
	if (f1.fail())
	{
		fprintf(stderr, "Error in read_graph()-1\n");
		exit(-1);
	}
	getline(f1, line);
	while (line.length() == 0 || line[0] == '%')
		getline(f1, line);

	stringstream ss(line);

	int n_typ = 0;
	ss >> n_vtx >> n_edg >> n_typ;

	// graph density
	long tt;
	tt = (long) n_vtx * ((long) n_vtx - 1) / 2;
	dens = (double) n_edg / (double) tt;

	adj_lst = new int*[ n_vtx ];
	adj_len = new int[ n_vtx ];
	int *tmpLst = new int[ n_vtx ];
	int len = 0, lno = 0;
	int vtx = 0;

	while (getline(f1, line))
	{
		if (f1.fail())
		{
			fprintf(stderr, "Error in read_graph()-2\n");
			exit(-1);
		}

		len = 0;
		stringstream ss(line);

		while (ss >> vtx)
			tmpLst[len++] = vtx - 1;
		adj_len[lno] = len;

		if (len == 0)
			adj_lst[lno] = NULL;
		else
		{
			adj_lst[lno] = new int[len];
			memcpy(adj_lst[lno], tmpLst, sizeof(int) * len);
		}

		lno++;
	}

	// allocate memory
	n_set = new int[ n_vtx ];
	f_set = new int[ n_vtx ];
	g_set = new int[ n_vtx ];
	mom = new int[ n_vtx ];
	dad = new int[ n_vtx ];
	cut_set = new int[ n_vtx ];
	cut_pos = new int[ n_vtx ];
	ttenure = new int[ n_vtx ];
	m_dis = new int[ PN+1 ];
	score = new double[ PN+1 ];
	fp = new long[ PN+1 ];
	deg_to = new int*[ 2 ];
	pop = new int*[ PN+1 ];
	p_dis = new int*[ PN+1 ];
	for (int i = 0; i < 2; i++)
		deg_to[i] = new int [ n_vtx ];
	for (int i = 0; i < PN+1; i++)
	{
		pop[i] = new int[ n_vtx ];
		p_dis[i] = new int[ PN+1 ];
		fp[i] = 0;
	}

	// free memory
	delete[] tmpLst;
	tmpLst = NULL;

	// for testing
	cout << "instance_name = " << instance_name << ", n_vtx = " << n_vtx << ", n_edg = " << n_edg << ", dens = " << dens << endl;
	cout << "finish reading" << endl;
	cout << "*******************************************************************************" << endl << endl;

	f1.close();
}


bool verify_size(int *set)
{
	s0 = vs1 = 0;
	for (int i = 0; i < n_vtx; i++)
	{
		if (set[i] == 0)
			s0 += 1;
		else
			vs1 += 1;
	}
	if (s0 == 0 || vs1 == 0)
		return true;
	else
		return false;
}


void verify_sol(int *set, long &f)
{
	//
	int cvol0 = 0, cvol1 = 0, ccut = 0;
	for (int i = 0; i < n_vtx; i++)
	{
		if (set[i] == 0)
		{
			cvol0 += adj_len[i];
			for (int j = 0; j < adj_len[i]; j++)
				if (set[adj_lst[i][j]] == 1)
					ccut += 1;
		}
		else
			cvol1 += adj_len[i];
	}
	if (vol0 != cvol0)
	{
		cout << "vol0 = " << vol0 << ", cvol0 = " << cvol0 << endl;
		fprintf(stderr, "Error vol0 in verify_sol()\n");
		exit(-1);
	}
	if (vol1 != cvol1)
	{
		cout << "vol1 = " << vol1 << ", cvol1 = " << cvol1 << endl;
		fprintf(stderr, "Error vol1 in verify_sol()\n");
		exit(-1);
	}
	if (cut != ccut)
	{
		cout << "cut = " << cut << ", ccut = " << ccut << endl;
		fprintf(stderr, "Error cut in verify_sol()\n");
		exit(-1);
	}

	//
	int **cdeg_to;
	cdeg_to = new int*[ 2 ];
	for (int i = 0; i < 2; i++)
		cdeg_to[i] = new int[ n_vtx ];

	for (int i = 0; i < n_vtx; i++)
	{
		cdeg_to[0][i] = 0;
		cdeg_to[1][i] = 0;
		for (int j = 0; j < adj_len[i]; j++)
			if (set[adj_lst[i][j]] == 0)
				cdeg_to[0][i]++;
			else
				cdeg_to[1][i]++;
	}
	for (int i = 0; i < n_vtx; i++)
	{
		if (deg_to[0][i] != cdeg_to[0][i])
		{
			cout << "Error no. = " << i << endl;
			fprintf(stderr, "Error deg_to[0][] in verify_sol()\n");
			exit(-1);
		}
		if (deg_to[1][i] != cdeg_to[1][i])
		{
			cout << "Error no. = " << i << endl;
			fprintf(stderr, "Error deg_to[1][] in verify_sol()\n");
			exit(-1);
		}
	}

	//
	long cf;
	cf = (double) ccut / (double) MIN(cvol0, cvol1) * MAX_INT;
	if (f != cf)
	{
		printf("f = %.8f, cf = %.8f\n", (double) f / MAX_INT, (double) cf / MAX_INT);
		fprintf(stderr, "Error f in verify_sol()\n");
		exit(-1);
	}

	// 1
	for (int i = 0; i < cs; i++)
	{
		if (cut_pos[cut_set[i]] != i)
		{
			cout << "Error no. = " << i << endl;
			fprintf(stderr, "Error cut_set[] and cut_pos[] in verify_sol()\n");
			exit(-1);
		}
	}

	// 2
	int k;
	for (int i = 0; i < cs; i++)
	{
		for (int j = i + 1; j < cs; j++)
		{
			if (cut_set[i] > cut_set[j])
			{
				k = cut_set[i];
				cut_set[i] = cut_set[j];
				cut_set[j] = k;
			}
		}
	}
	for (int i = 0; i < n_vtx; i++)
		cut_pos[i] = -1;
	for (int i = 0; i < cs; i++)
		cut_pos[cut_set[i]] = i;

	int ccs = 0;
	int *ccut_set, *ccut_pos;
	ccut_set = new int[ n_vtx ];
	ccut_pos = new int[ n_vtx ];
	for (int i = 0; i < n_vtx; i++)
		ccut_pos[i] = -1;
	for (int i = 0; i < n_vtx; i++)
	{
		for (int j = 0; j < adj_len[i]; j++)
		{
			if (set[i] != set[adj_lst[i][j]])
			{
				ccut_pos[i] = ccs;
				ccut_set[ccs++] = i;
				break;
			}
		}
	}
	for (int i = 0; i < n_vtx; i++)
	{
		if (cut_pos[i] != ccut_pos[i])
		{
			cout << "Error no. = " << i << endl;
			fprintf(stderr, "Error cut_pos[] in verify_sol()\n");
			exit(-1);
		}
	}
	for (int i = 0; i < cs; i++)
	{
		if (cut_set[i] != ccut_set[i])
		{
			cout << "Error no. = " << i << endl;
			fprintf(stderr, "Error cut_set[] in verify_sol()\n");
			exit(-1);
		}
	}

	//free memory
	for (int i = 0; i < 2; i++)
	{
		delete[] cdeg_to[i];
		cdeg_to[i] = NULL;
	}
	delete[] cdeg_to;
	delete[] ccut_set;
	delete[] ccut_pos;
	cdeg_to = NULL;
	ccut_set = NULL;
	ccut_pos = NULL;
}


void verify_final_result(int *set, long &f)
{
	long final_best;

	vol0 = vol1 = s0 = vs1 = cut = 0;
	for (int i = 0; i < n_vtx; i++)
	{
		if (set[i] == 0)
		{
			s0++;
			vol0 += adj_len[i];
			for (int j = 0; j < adj_len[i]; j++)
				if (set[adj_lst[i][j]] == 1)
					cut += 1;
		}
		else
		{
			vs1++;
			vol1 += adj_len[i];
		}
	}
	final_best = (double) cut / (double) MIN(vol0, vol1) * MAX_INT;

	if (final_best != f)
	{
		cout << "Find a error solution!" << endl;
		printf("final_sol = %.8f", (double) final_best / (double) MAX_INT);
		printf(", while f = %.8f\n", (double) f / (double) MAX_INT);
		exit(0);
	}
}


void cut_set_update(int *set, int &vtx)
{
	int k;

	//from V\S to S
	if (set[vtx] == 1)
	{
		//vtx is not in the cut set
		if (deg_to[0][vtx] == 0)
		{
			//add itself
			cut_set[cs] = vtx;
			cut_pos[vtx] = cs;
			cs++;

			for (int i = 0; i < adj_len[vtx]; i++)
			{
				k = adj_lst[vtx][i];
				if (deg_to[1][k] == 0)
				{
					fprintf(stderr, "Error in cut_set_update()-1\n");
					exit(-1);
				}
				if (deg_to[0][k] == 0)
				{
					cut_set[cs] = k;
					cut_pos[k] = cs;
					cs++;
				}
			}
		}
		//vtx is in the cut set
		else
		{
			//consider itself
			if (deg_to[1][vtx] == 0)
			{
				cut_set[cut_pos[vtx]] = cut_set[cs - 1];
				cut_pos[cut_set[cs - 1]] = cut_pos[vtx];
				cut_pos[vtx] = -1;
				cs--;
			}
			//consider its neighborhood
			for (int i = 0; i < adj_len[vtx]; i++)
			{
				k = adj_lst[vtx][i];
				if (set[k] == 1 && deg_to[0][k] == 0)
				{
					cut_set[cs] = k;
					cut_pos[k] = cs;
					cs++;
				}
				if (set[k] == 0 && deg_to[1][k] == 1)
				{
					cut_set[cut_pos[k]] = cut_set[cs - 1];
					cut_pos[cut_set[cs - 1]] = cut_pos[k];
					cut_pos[k] = -1;
					cs--;
				}
			}
		}
	}//end from V\S to S

	//from S to V\S
	if (set[vtx] == 0)
	{
		//vtx is not in the cut set
		if (deg_to[1][vtx] == 0)
		{
			//add itself
			cut_set[cs] = vtx;
			cut_pos[vtx] = cs;
			cs++;

			for (int i = 0; i < adj_len[vtx]; i++)
			{
				k = adj_lst[vtx][i];
				if (deg_to[0][k] == 0)
				{
					fprintf(stderr, "Error in cut_set_update()-2\n");
					exit(-1);
				}
				if (deg_to[1][k] == 0)
				{
					cut_set[cs] = k;
					cut_pos[k] = cs;
					cs++;
				}
			}
		}
		//vtx is in the cut set
		else
		{
			//consider itself
			if (deg_to[0][vtx] == 0)
			{
				cut_set[cut_pos[vtx]] = cut_set[cs - 1];
				cut_pos[cut_set[cs - 1]] = cut_pos[vtx];
				cut_pos[vtx] = -1;
				cs--;
			}
			//consider its neighborhood
			for (int i = 0; i < adj_len[vtx]; i++)
			{
				k = adj_lst[vtx][i];
				if (set[k] == 0 && deg_to[1][k] == 0)
				{
					cut_set[cs] = k;
					cut_pos[k] = cs;
					cs++;
				}
				if (set[k] == 1 && deg_to[0][k] == 1)
				{
					cut_set[cut_pos[k]] = cut_set[cs - 1];
					cut_pos[cut_set[cs - 1]] = cut_pos[k];
					cut_pos[k] = -1;
					cs--;
				}
			}
		}
	}//end from S to V\S
}


// initialize
void initialize(int *set, long &f)
{
	cut = vol0 = vol1 = 0;
	s0 = vs1 = cs = 0;

	for (int i = 0; i < n_vtx; i++)
	{
		if (set[i] == 0)
		{
			vol0 += adj_len[i];
			s0++;
			for (int j = 0; j < adj_len[i]; j++)
				if (set[adj_lst[i][j]] == 1)
					cut++;
		}
		else
		{
			vol1 += adj_len[i];
			vs1++;
		}
	}

	for (int i = 0; i < n_vtx; i++)
	{
		deg_to[0][i] = 0;
		deg_to[1][i] = 0;
		for (int j = 0; j < adj_len[i]; j++)
		{
			if (set[adj_lst[i][j]] == 0)
				deg_to[0][i]++;
			else
				deg_to[1][i]++;
		}
	}

	for (int i = 0; i < n_vtx; i++)
	{
		cut_pos[i] = -1;
		for (int j = 0; j < adj_len[i]; j++)
		{
			if (set[i] != set[adj_lst[i][j]])
			{
				cut_set[cs] = i;
				cut_pos[i] = cs++;
				break;
			}
		}
	}

	f = (double) cut / (double) MIN(vol0, vol1) * MAX_INT;
}


// = 0 means the solution is different
// = 1 means the solution is identical(symmetric)
int is_duplicate(int*set, int &k)
{
    int m, n;

    for (int i = 0; i < k; i++)
    {
        m = n = 0;

//      if (fbest < fp[k])
//        	return 0;

        for (int j = 0; j < n_vtx; j++)
        {
        	if (set[j] == pop[i][j])  // identical
            	m++;
            if (set[j] != pop[i][j])  // symmetric
            	n++;
        }

        if (m == n_vtx || n == n_vtx)
          return 1;
    }

    return 0;
}


// distance between two solutions in Pop, only used in ini_pop()
int distance_two(int &p1, int &p2)
{
	int i, j, k;
	i = j = k = 0;

	while (i < n_vtx && j < n_vtx)
	{
		if (pop[p1][i] == pop[p2][j])
		{
			k++;
			i++;
			j++;
		}
		else
		{
			i++;
			j++;
		}
	}

	return (n_vtx - k);
}


// distance between f_set[] (best solution) and pop
int distance_pop(int *set, int p)
{
	int i, j, k;
	i = j = k = 0;

	while (i < n_vtx && j < n_vtx)
	{
		if (pop[p][i] == set[j])
		{
			k++;
			i++;
			j++;
		}
		else
		{
			i++;
			j++;
		}
	}

	return (n_vtx - k);
}


void read_MQI(char *filename, int &k)
{
	string line;
	ifstream ff(filename);
	if (ff.fail())
	{
		fprintf(stderr, "Error in read_MQI()-1\n");
		exit(-1);
	}

	for (int i = 0; i < n_vtx; i++)
		f_set[i] = 1;

	int num, v;
	getline(ff, line);
	stringstream ss(line);
	ss >> num;

	while (getline(ff, line))
	{
		if (ff.fail())
		{
			fprintf(stderr, "Error in read_MQI()-2\n");
			exit(-1);
		}
		stringstream ss(line);

		ss >> v;
		f_set[v] = 0;
	}

	ff.close();
}


void construct_sol()
{
	int vtx = rand() % n_vtx;

	for (int i = 0; i < n_vtx; i++)
	{
		if (vtx != i)
			f_set[i] = 1;
		else
			f_set[i] = 0;
	}
}


void initial_pop()
{
	for (int k = 0; k < PN; k++)
	{
		if ((static_cast<double>(rand() % 101) / 100.0) < 0.5)
			construct_sol();
		else
		{
			sprintf(MQI_path, "./MQI/%s/%s/%s_result_%d.smat", data_set, instance_name, instance_name, k);
			read_MQI(MQI_path, k);
		}

		// improved by tabu search
		initialize(f_set, fbest);
		tabu_search(f_set, fbest, ftime);

		cout << "k = " << k << "-";
		printf("fbest = %.8lf, ", (double) fbest / (double) MAX_INT);
		printf("ftime = %.2lf\n", ftime);

		// update global best
		if (fbest < gbest)
		{
			gbest = fbest;
			gtime = ftime;
			for (int i = 0; i < n_vtx; i++)
				g_set[i] = f_set[i];
		}
		printf("gbest = %.8lf, ", (double) gbest / (double) MAX_INT);
		printf("gtime = %.2lf\n\n", gtime);

		// fp[k] == 0, make the pop always have PN solutions in initialize
		if (is_duplicate(f_set, k) == 0 || fp[k] == 0)
		{
			fp[k] = fbest;  // must fbest, = current sol.

			for (int i = 0; i < n_vtx; i++)
				pop[k][i] = f_set[i];
		}

		if ((clock() - start_time) / CLOCKS_PER_SEC > run_time)
			break;
	}

	for (int i = 0; i < PN; i++)
	{
		for (int j = i + 1; j < PN; j++)
			p_dis[i][j] = p_dis[j][i] = distance_two(i, j);
		p_dis[i][i] = n_vtx + 100;
	}
}


// randomly select two different parent solutions
void select_parent()
{
	int k = 0, p, flag;

	while (k < 2)
	{
		flag = 0;
		p = rand() % PN;
		for (int i = 0; i < k; i++)
		{
			if (p == parent[i])
			{
				flag = 1;
				break;
			}
		}
		if (flag == 0)
			parent[k++] = p;
	}

	for (int i = 0; i < n_vtx; i++)
	{
		mom[i] = pop[parent[0]][i];
		dad[i] = pop[parent[1]][i];
	}
}


void double_cutting_point_crossover(int *set1, int *set2, long &f1, long &f2)
{
	int aa, bb;
	int *m0, *m1;

	aa = rand() % n_vtx;
	bb = aa + rand() % (n_vtx - aa);
	m0 = new int[ n_vtx ];
	m1 = new int[ n_vtx ];

	for (int i = 0; i < aa; i++)
	{
		m0[i] = 1;
		m1[i] = 0;
	}
	for (int i = aa; i < bb; i++)
	{
		m0[i] = 0;
		m1[i] = 1;
	}
	for (int i = bb; i < n_vtx; i++)
	{
		m0[i] = 1;
		m1[i] = 0;
	}

	for (int i = 0; i < n_vtx; i++)
		f_set[i] = (mom[i] & m0[i])|(dad[i] & m1[i]);
	for(int i = 0; i < n_vtx; i++)
		n_set[i] = (mom[i] & m1[i])|(dad[i] & m0[i]);

	// free memory
	delete[] m0;
	delete[] m1;
	m0 = NULL;
	m1 = NULL;
}


void delta_update_add(int *set, int &k)
{
	if (set[k] == 0)
	{
		vol0 -= adj_len[k];
		vol1 += adj_len[k];
		s0--;
		vs1++;
		cut = cut + deg_to[0][k] - deg_to[1][k];

		cut_set_update(set, k);

		for (int i = 0; i < adj_len[k]; i++)
		{
			deg_to[0][adj_lst[k][i]] -= 1;
			deg_to[1][adj_lst[k][i]] += 1;
		}

		set[k] = 1;
	}
	else
	{
		vol0 += adj_len[k];
		vol1 -= adj_len[k];
		s0++;
		vs1--;
		cut = cut - deg_to[0][k] + deg_to[1][k];

		cut_set_update(set, k);

		for (int i = 0; i < adj_len[k]; i++)
		{
			deg_to[0][adj_lst[k][i]] += 1;
			deg_to[1][adj_lst[k][i]] -= 1;
		}

		set[k] = 0;
	}
}


void evaluate_add(int *set, int &len)
{
	int id, k;
	int c, v0, v1;
	long sol;

	best_sol = tabu_sol = MAX_INT;
	best_len = tabu_len = 0;

	for (int i = 0; i < len; i++)
	{
		id = rand() % cs;
		k = cut_set[id];

		if (set[k] == 0 && s0 > 1)
		{
			v0 = vol0 - adj_len[k];
			v1 = vol1 + adj_len[k];
			c = cut + deg_to[0][k] - deg_to[1][k];
		}
		else if (set[k] == 1 && vs1 > 1)
		{
			v0 = vol0 + adj_len[k];
			v1 = vol1 - adj_len[k];
			c = cut - deg_to[0][k] + deg_to[1][k];
		}
		else
			continue;

		sol = (double) c / (double) MIN(v0, v1) * MAX_INT;

		//if it is tabu
		if (iter < ttenure[k])
		{
			if (sol < tabu_sol)
			{
				tabu_sol = sol;
				tabu_add[0] = k;
				tabu_len = 1;
			}
			else if (sol == tabu_sol && tabu_len < 100000)
			{
				tabu_add[tabu_len] = k;
				tabu_len++;
			}
		}
		//if it is not tabu
		else
		{
			if (sol < best_sol)
			{
				best_sol = sol;
				best_add[0] = k;
				best_len = 1;
			}
			else if (sol == best_sol && best_len < 100000)
			{
				best_add[best_len] = k;
				best_len++;
			}
		}
	}// for
}


void tabu_search(int *now_set, long &nowbest, double &nowtime)
{
	int id, k, len;
	long f;
	int *set;

	// tabu tenure management
	int p = 0, t = 0;
	const int periods = 15;                   // the number of periods
	const int p_interval = TD / periods;      // the intervals = TD / 15
	int B[periods] = { 10, 20, 10, 40, 10, 20, 10, 80, 10, 20, 10, 40, 10, 20, 10 };
	int A[periods];
	for (int i = 0; i < periods; i++)
		A[i] = alfa;

	iter = 0;
	len = 1;
	f = nowbest;
	set = new int[ n_vtx ];
	for (int i = 0; i < n_vtx; i++)
	{
		set[i] = now_set[i];
		ttenure[i] = 0;
	}

	while (iter < TD)
	{
		evaluate_add(set, len);

		// if the solution of all evaluated nodes = 1,
		// reset and to the next while loop
		if (tabu_len == 0 && best_len == 0)
			break;

		// accept tabu solution, (1) aspiration criterion, (2) no improved sol in non-tabu nodes
		if ((tabu_len > 0 && tabu_sol <= best_sol && tabu_sol <= nowbest) || (best_len == 0))
		{
			id = rand() % tabu_len;
			k = tabu_add[id];
			f = tabu_sol;
		}
		else
		{
			id = rand() % best_len;
			k = best_add[id];
			f = best_sol;
		}
		delta_update_add(set, k);

		// update tabu tenure
		ttenure[k] = A[p] * B[p] + iter;
		t++;
		if (t > p_interval)
		{
			p = (p + 1) % periods;
			t = 0;
		}

		if (f < nowbest)
		{
			nowbest = f;
			nowtime = (clock() - start_time) / CLOCKS_PER_SEC;
			for (int i = 0; i < n_vtx; i++)
				now_set[i] = set[i];
			iter = 0;
			len = 1;
		}
		else
		{
			iter++;
			len++;
			if (len > cs)
				len = 1;
		}

		/*if (iter % 100 == 0)
		{
			cout << "add-iter = " << iter << endl;
			printf("best = %.8lf\n", (double) nowbest / (double) MAX_INT);
			printf("time = %.2lf\n\n", nowtime);
		}*/

		if ((clock() - start_time) / CLOCKS_PER_SEC > run_time)
			break;
	}

	// free memory
	delete[] set;
	set = NULL;
}


void mutation(int *set, long &f, int &step)
{
	int k;

	for (int i = 0; i < n_vtx; i++)
		set[i] = f_set[i];

	s0 = vs1 = 0;
	for (int i = 0; i < n_vtx; i++)
	{
		if (set[i] == 0)
			s0++;
		else
			vs1++;
	}

	for (int i = 0; i < step; i++)
	{
		k = rand() % n_vtx;
		if (set[k] == 0 && s0 > 1)
		{
			set[k] = 1 - set[k];
			s0--;
			vs1++;
		}
		else if (set[k] == 1 && vs1 > 1)
		{
			set[k] = 1 - set[k];
			s0++;
			vs1--;
		}
		else
			continue;
	}

	initialize(set, f);

	if (f < gbest)
	{
		gbest = f;
		gtime = (clock() - start_time) / CLOCKS_PER_SEC;
		for (int i = 0; i < n_vtx; i++)
			g_set[i] = set[i];
	}
}


// identify the worst solution in pop with the maximum goodness score
void max_distance(int *set, long &f, int &k1, int &k2)
{
	int d;

	// add best sol. to pop[PN][n_vtx], then update distance of pop'[PN+1][n_vtx]
	// i.e. update the distance between any two solutions in the pop
	for (int i = 0; i < PN; i++)
	{
		d = distance_pop(set, i);  // distance between set[] (current best solution) and pop
		p_dis[i][PN] = p_dis[PN][i] = d;
	}
	p_dis[PN][PN] = n_vtx + 100;

	// calculate the distance between solution in pop' and pop' (min distance)
	for (int i = 0; i < PN + 1; i++)
	{
		d = n_vtx + 100;
		for (int j = 0; j < PN + 1; j++)
			if (i != j && p_dis[i][j] < d)
				d = p_dis[i][j];
		m_dis[i] = d;
	}
	fp[PN] = f;

	// the goodness score function
	// the min and max value of m_dis[PN+1]
	int DS_min = n_vtx + 10;
	int DS_max = -1;
	// the min and max value of fp[PN+1]
	long FS_min = MAX_INT;
    long FS_max = -1;

	for (int i = 0; i < PN + 1; i++)
	{
		if (m_dis[i] > DS_max)
			DS_max = m_dis[i];
		if (m_dis[i] < DS_min)
			DS_min = m_dis[i];

		if (fp[i] > FS_max)
			FS_max = fp[i];
		if (fp[i] < FS_min)
			FS_min = fp[i];
	}

	// denominator of A()
	long FS_D = FS_max - FS_min + 1;
	int DS_D = DS_max - DS_min + 1;

	for (int i = 0; i < PN + 1; i++)
		score[i] = (6 * (fp[i] - FS_min) / double(FS_D)
				 + 4 * (m_dis[i] - DS_min) / double(DS_D)) * MAX_INT;

	// identify the worst solution in pop with the maximum goodness score
	double bad_max = -1;
	for (int i = 0; i < PN + 1; i++)
	{
		if (score[i] > bad_max)
		{
			bad_max = score[i];
			k1 = i;
		}
	}

	// identify the *second* worst solution in pop
	bad_max = -1;
	for (int i = 0; i < PN + 1; i++)
	{
		if (i != k1 && score[i] > bad_max)
		{
			bad_max = score[i];
			k2 = i;
		}
	}
}


void update_pop(int *set, long &f)
{
	int k1, k2;

	max_distance(set, f, k1, k2);

	if (k1 != PN && is_duplicate(set, PN) == 0)
	{
		fp[k1] = f;
		for (int i = 0; i < n_vtx; i++)
			pop[k1][i] = set[i];

		for (int i = 0; i < PN; i++)
			p_dis[k1][i] = p_dis[i][k1] = p_dis[PN][i];

		p_dis[k1][k1] = n_vtx + 100;
	}

	if ((static_cast<double>(rand() % 101) / 100.0) < 0.5)
	{
		if (k2 != PN && is_duplicate(set, PN) == 0)
		{
			fp[k2] = f;
			for (int i = 0; i < n_vtx; i++)
				pop[k2][i] = set[i];

			for (int i = 0; i < PN; i++)
				p_dis[k2][i] = p_dis[i][k2] = p_dis[PN][i];

			p_dis[k2][k2] = n_vtx + 100;
		}
	}
}


void Mem_Alg()
{
	bool flag1, flag2;
	int generation = 0;

	while ((clock() - start_time) / CLOCKS_PER_SEC < run_time)
	{
		flag1 = flag2 = true;
		while (flag1 || flag2)
		{
			select_parent();
			double_cutting_point_crossover(f_set, n_set, fbest, nbest);
			flag1 = verify_size(f_set);
			flag2 = verify_size(n_set);
			if (flag1 || flag2)
			{
				cout << "flag1 = " << flag1 << ", flag2 = " << flag2 << endl;
				cout << "try again!" << endl;
			}
		}

		// First trajectory
		initialize(f_set, fbest);
		tabu_search(f_set, fbest, ftime);
		update_pop(f_set, fbest);
		if (fbest < gbest)
		{
			gbest = fbest;
			gtime = ftime;
			for (int i = 0; i < n_vtx; i++)
				g_set[i] = f_set[i];
		}

		// Second trajectory
		initialize(n_set, nbest);
		tabu_search(n_set, nbest, ntime);
		update_pop(n_set, nbest);
		if (nbest < gbest)
		{
			gbest = nbest;
			gtime = ntime;
			for (int i = 0; i < n_vtx; i++)
				g_set[i] = n_set[i];
		}

		cout << "- " << generation << " -" << endl;
		cout << "cs = " << cs << endl;
		cout << "vol0:vol1 = " << vol0 << ":" << vol1 << endl;
		cout << "s0:vs1 = " << s0 << ":" << vs1 << endl;
		printf("fbest = %.8lf, ", (double) fbest / (double) MAX_INT);
		printf("ftime = %.2lf\n", ftime);
		printf("nbest = %.8lf, ", (double) nbest / (double) MAX_INT);
		printf("ntime = %.2lf\n", ntime);
		printf("gbest = %.8lf, ", (double) gbest / (double) MAX_INT);
		printf("gtime = %.2lf\n", gtime);
		cout << "fp[] = ";
		for (int i = 0; i < PN; i++)
			printf("%.8lf ", (double) fp[i] / (double) MAX_INT);
		cout << endl << endl;
		generation++;

		if ((clock() - start_time) / CLOCKS_PER_SEC > run_time)
			break;
	}
}


void Main_Mem_Alg()
{
	fbest = nbest = gbest = MAX_INT;
	ftime = ntime = gtime = 0.0;
	start_time = clock();

	for (int k = 0; k < 1; k++)
	{
		initial_pop();

		//***********************************************************
		cout << endl << "finish initializing" << endl;
		printf("gbest = %.8lf, ", (double) gbest / (double) MAX_INT);
		printf("gtime = %.2lf\n", gtime);
		cout << "fp[] = ";
		for (int i = 0; i < PN; i++)
			printf("%.8lf ", (double) fp[i] / (double) MAX_INT);
		cout << endl << "---------------------------------------" << endl << endl;

		//***********************************************************

		Mem_Alg();

		//***********************************************************
		cout << "finish memetic" << endl;
		printf("gbest = %.8lf, ", (double) gbest / (double) MAX_INT);
		printf("gtime = %.2lf\n\n", gtime);
		cout << "fp[] = ";
		for (int i = 0; i < PN; i++)
			printf("%.8lf ", (double) fp[i] / (double) MAX_INT);
		cout << endl;
		cout << "score[] = ";
		for (int i = 0; i < PN; i++)
			printf("%.8lf ", (double) score[i] / (double) MAX_INT);
		cout << endl;
		cout << "m_dis[] = ";
		for (int i = 0; i < PN; i++)
			cout << m_dis[i] << " ";
		cout << endl;
		cout << "p_dis[][] = " << endl;
		for (int i = 0; i < PN; i++)
		{
			for (int j = 0; j < PN; j++)
				cout << p_dis[i][j] << " ";
			cout << endl;
		}
		cout << "*******************************************************************************" << endl;
		cout << endl << endl;

		//***********************************************************
	}
}


void free_memory()
{
	delete[] n_set;
	delete[] f_set;
	delete[] g_set;
	delete[] dad;
	delete[] mom;
	delete[] ttenure;
	delete[] fp;
	delete[] m_dis;
	delete[] score;
	delete[] cut_set;
	delete[] cut_pos;

	n_set = NULL;
	f_set = NULL;
	g_set = NULL;
	dad = NULL;
	mom = NULL;
	ttenure = NULL;
	fp = NULL;
	m_dis = NULL;
	score = NULL;
	cut_set = NULL;
	cut_pos = NULL;

	for (int i = 0; i < 2; i++)
	{
		delete[] deg_to[i];
		deg_to[i] = NULL;
	}
	delete[] deg_to;
	deg_to = NULL;

	for (int i = 0; i < n_vtx; i++)
	{
		delete[] adj_lst[i];
		adj_lst[i] = NULL;
	}
	delete[] adj_lst;
	adj_lst = NULL;
	delete[] adj_len;
	adj_len = NULL;

	for (int i = 0; i < PN + 1; i++)
	{
		delete[] pop[i];
		pop[i] = NULL;
		delete[] p_dis[i];
		p_dis[i] = NULL;
	}
	delete[] pop;
	pop = NULL;
	delete[] p_dis;
	p_dis = NULL;
}


int main(int argc, char* argv[])
{
	FILE *statistic;
	FILE *result;
	FILE *out;

	if (argc == 7)
	{
		instance_name = argv[1];
		data_set = argv[2];
		run_time = atoi(argv[3]);
		run_num = atoi(argv[4]);
		TD = atoi(argv[5]);
		alfa = atof(argv[6]);
	}
	else
	{
		printf("\n### Input the following parameters ###\n");
		printf("<instance_name> <data_set> <run_time> <run_num> <TD> <alfa>\n");
		exit(-1);
	}

	// there are 2 types of file path: instances, statistics
	sprintf(instance_path, "./instances/%s/%s.graph", data_set, instance_name);
	sprintf(statistic_path, "./statistics/%s/%s.statistic", data_set, instance_name);

	// OPEN in statistical file
	if ((statistic = fopen(statistic_path, "w")) == NULL)
	{
		printf("Open failed for output %s\n", statistic_path);
		exit(1);
	}
	fprintf(statistic, "maximum run time = %d(s), number of repeat = %d\n", run_time, run_num);
	fprintf(statistic, "---------------------------------------------------------\n");

	int count;
	long best_sol, worst_sol;
	double avg_sol, avg_time, sd;
	long total_sol[run_num];
	double total_time[run_num];

	// read the graph
	read_graph(instance_path);

	for (int i = 0; i < run_num; i++)
	{
		cout << "-" << i << "-" << endl;

		// set random seed
		seed = (unsigned) time(NULL);
		srand(seed);

		Main_Mem_Alg();
//		verify_final_result();

		total_sol[i] = gbest;
		total_time[i] = gtime;

		// WRITE in statistical file
		fprintf(statistic, "%.8lf, %.4lf, %4d\n", (double) gbest / (double) MAX_INT, gtime, i);

		// WRITE final result set in file
		sprintf(result_path, "./results/%s/%s/%s_result_%d.smat", data_set, instance_name, instance_name, i);
		result = fopen(result_path, "w+");
		for (int j = 0; j < n_vtx; j++)
			fprintf(result, "%d\n", g_set[j]);
		fclose (result);
	}

	count = 0;
	best_sol = MAX_INT;
	worst_sol = 0;
	avg_sol = avg_time = sd = 0.0;
	// average data
	for (int i = 0; i < run_num; i++)
	{
		avg_time += total_time[i];
		avg_sol += total_sol[i];
	}
	avg_time /= run_num;
	avg_sol /= run_num;

	// best data, worst data, success rate, sd
	for (int i = 0; i < run_num; i++)
	{
		if (total_sol[i] < best_sol)
			best_sol = total_sol[i];

		if (total_sol[i] > worst_sol)
			worst_sol = total_sol[i];
	}
	for (int i = 0; i < run_num; i++)
	{
		if (total_sol[i] == best_sol)
			count += 1;
	}
	for (int i = 0; i < run_num; i++)
		sd += pow((total_sol[i] - avg_sol), 2);
	sd /= run_num;
	sd = sqrt(sd);

	fprintf(statistic, "---------------------------------------------------------\n");
	fprintf(statistic, "%s, %d, %d, %d(s)*%d(times), %.8lf, %.8lf, %.8lf, %.4lf(s), %d//%d, %.8lf\n",
			instance_name, n_vtx, n_edg, run_time, run_num,
			(double) best_sol / (double) MAX_INT,
			(double) avg_sol / (double) MAX_INT,
			(double) worst_sol / (double) MAX_INT,
			avg_time, count, run_num,
			(double) sd / (double) MAX_INT);
	fclose(statistic);

	// output for excel
	sprintf(final_result_path, "./final_result.xlsx");
	if ((out = fopen(final_result_path, "a+")) == NULL)
	{
		printf("Open failed for output %s\n", final_result_path);
		exit(1);
	}
	fprintf(out, "%s, %d, %d, %d(s)*%d(times), %.8lf, %.8lf, %.8lf, %.4lf(s), %d//%d, %.8lf\n",
			instance_name, n_vtx, n_edg, run_time, run_num,
			(double) best_sol / (double) MAX_INT,
			(double) avg_sol / (double) MAX_INT,
			(double) worst_sol / (double) MAX_INT,
			avg_time, count, run_num,
			(double) sd / (double) MAX_INT);
	fclose(out);

	//***********************************************************
	printf("\nInstance: %s, nodes: %d, edges: %d\n", instance_name, n_vtx, n_edg);
	printf("The fbest: %.8lf\n", (double) best_sol / (double) MAX_INT);
	printf("The favg: %.8lf\n", (double) avg_sol / (double) MAX_INT);
	printf("The fworst: %.8lf\n", (double) worst_sol / (double) MAX_INT);
	printf("The hit time: %.4lf\n", avg_time);
	printf("The success rate: %d//%d\n", count, run_num);
	printf("The sd: %.8lf\n", (double) sd / (double) MAX_INT);
	//***********************************************************

	// free memory
	free_memory();

	return 0;
}

