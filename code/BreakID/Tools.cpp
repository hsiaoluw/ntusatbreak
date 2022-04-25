/*
 * Tools.cpp
 *
 *  Created on: Jan 23, 2013
 *      Author: jodv
 */

#include "Tools.h"
#include "Symmetry.h"
#include "SymmetryGroup.h"
#include "Translator.h"
#include "string.h"
#include <iostream>
#include <fstream>

namespace sym {

unsigned int verbosity = 1;
unsigned int maxMemory = 2000;
unsigned int maxTime = 100;
double usedTime = 0.0;
unsigned int nrSymGroups = 0;

int dimacs2lit(int in) {
	assert(in!=0);
	return in;
}

int lit2dimacs(int in) {
	return in;
}

vector<string>& split1(string& s, char delim, vector<string>& elems) {
	stringstream ss(s);
	string item;
	while (getline(ss, item, delim)) {
		if (item.size() > 0) {
			elems.push_back(item);
		}
	}
	return elems;
}

vector<string> split2(string &s, char delim) {
	vector<string> elems;
	return split1(s, delim, elems);
}

void parseCycle(string& cycle, vector<int> & result) {
	vector<string> litStrings = split2(cycle, ' ');
	for (string s : litStrings) {
		int tmp = atoi(s.c_str());
		result.push_back(dimacs2lit(tmp));
	}
}

void parseSymmetry(string& line, map<int, int>& values) {
	values.clear();
	auto cycles = split2(line, '(');
	for (auto c : cycles) {
		c = c.substr(0, c.size() - 1); // TODO: C++11: cycles[i].pop_back();
		vector<int> cycle;
		parseCycle(c, cycle);
		if (cycle.size() > 1) {
			for (unsigned int i = 0; i < cycle.size(); ++i) {
				values.insert( { cycle[i], cycle[(i + 1) % cycle.size()] });
			}
		}
	}
}

bool commutesWithNegation(map<int, int>& sym) {
	for (auto litpair : sym) {
		if (neg(sym[litpair.first]) != sym[neg(litpair.first)]) {
			// not(sym(lit))!=sym(not(lit))
			return false;
		}
	}
	return true;
}

void readSymmetries(string& path, shared_ptr<Translator> trans, vector<shared_ptr<SymmetryGroup> >& symGroups) {
	vector<shared_ptr<map<unsigned int, int> > > syms;

	string line;
	ifstream file;
	file.open(path);
	while (getline(file, line)) {
		map<int, int> tmpSym;
		parseSymmetry(line, tmpSym);
		if (not commutesWithNegation(tmpSym)) {
			if (verbosity > 0) {
				cout << "Warning: symmetry that does not commute with negation has been ignored.\n";
			}
		} else {
			shared_ptr<map<unsigned int, int> > newSym = make_shared<map<unsigned int, int> >();
			for (auto litpair : tmpSym) {
				if (not sign(litpair.first)) {
					assert(litpair.first>0);
					assert(litpair.second!=0);
					newSym->insert(litpair); //{litpair.first, litpair.second});
					assert(newSym->at(litpair.first)!=0);
				}
			}
			syms.push_back(newSym);
		}
	}

	vector<vector<shared_ptr<map<unsigned int, int> > > > symPartitions;
	for (auto sym : syms) {
		symPartitions.push_back(vector<shared_ptr<map<unsigned int, int> > >());
		symPartitions.back().push_back(sym);
	}

	for (int i = symPartitions.size() - 1; i >= 0; --i) {
		for (int j = i - 1; j >= 0; --j) {
			bool independent = true;
			if (not independent) {
				break;
			}
			for (auto sym1 : symPartitions.at(i)) {
				if (not independent) {
					break;
				}
				for (auto sym2 : symPartitions.at(j)) {
					if (not areIndependent(sym1, sym2)) {
						independent = false;
						break;
					}
				}
			}
			if (not independent) {
				for (auto sym1 : symPartitions.at(i)) {
					symPartitions.at(j).push_back(sym1);
				}
				symPartitions[i] = symPartitions.back();
				symPartitions.pop_back();
				break;
			}
		}
	}

	for (auto sympart : symPartitions) {
		symGroups.push_back(make_shared<SymmetryGroup>(sympart, trans));
	}
}

shared_ptr<Translator> readCNF(string& path, string& outFile) {
	bool readingClauses = false;
	int numVars = 0;
	int numClauses = 0;
	string clauseString = "";
	string line;

	ifstream file;
	file.open(path);
	while (getline(file, line)) {
		if (line.front() == 'p') {
			vector<string> pline = split2(line, ' ');
			assert(pline.size()==4);
			assert(pline[0]=="p");
			assert(pline[1]=="cnf");
			numVars = dimacs2lit(atoi(pline[2].c_str()));
			numClauses = atoi(pline[3].c_str());
			readingClauses = true;
			if (verbosity > 0) {
				cout << "numVars: " << numVars << " numClauses: " << numClauses << endl;
			}
		} else if (readingClauses) {
			clauseString += line + "\n";
		} else {
			// reading comments before p-line
		}
	}
	file.close();
	assert(readingClauses);
	return make_shared<Translator>(numVars, numClauses, clauseString, outFile);
}

bool compareSymmetry(shared_ptr<Symmetry> first, shared_ptr<Symmetry> second) {
	return first->compareTo(second) > 0;
}

bool areIndependent(shared_ptr<map<unsigned int, int> > sym1, shared_ptr<map<unsigned int, int> > sym2) {
	for (auto paar : *sym1) {
		if ((int) paar.first != paar.second && sym2->count(paar.first) && (int) paar.first != sym2->at(paar.first)) {
			return false;
		}
	}
	return true;
}

void removeOverlappingSyms(unordered_set<int>& lits, vector<shared_ptr<Symmetry> >& syms) {
	for (unsigned int i = 0; i < syms.size(); ++i) {
		for (unsigned int j = 0; j < syms.at(i)->supportSize(); ++j) {
			if (lits.count(syms.at(i)->get(j)) != 0 || lits.count(neg(syms.at(i)->get(j))) != 0) {
				syms[i] = syms.back();
				syms.pop_back();
				--i;
				break;
			}
		}
	}
}

#include <utility>

vector<pair<unsigned int, unsigned int> > factor_table;
void fill_sieve(unsigned int n) {
	factor_table.resize(n + 1);
	for (unsigned int i = 1; i <= n; ++i) {
		if (i & 1)
			factor_table[i] = pair<unsigned int, unsigned int>(i, 1);
		else
			factor_table[i] = pair<unsigned int, unsigned int>(2, i >> 1);
	}
	for (unsigned int j = 3, j2 = 9; j2 <= n;) {
		if (factor_table[j].second == 1) {
			unsigned int i = j;
			unsigned int ij = j2;
			while (ij <= n) {
				factor_table[ij] = pair<unsigned int, unsigned int>(j, i);
				++i;
				ij += j;
			}
		}
		j2 += (j + 1) << 2;
		j += 2;
	}
	/**	generates a table with the following properties:
	 !i: i/table[i].first=table[i].second
	 !i,j: i%j==0 => table[i].first=<j.

	 but we need a table which adheres to:
	 !i: ?n: i/(table[i].first^n)=table[i].second
	 !i,j: i%j==0 => table[i].first=<j.
	 **/

	// we utilize that !i,j: i%j==0 => table[i].first=<j.
	// <=> the table always lists the smallest prime factor, so to deduplicate factors,
	// we only need to check whether it still occurrs in the resulting division.
	for (unsigned int i = factor_table.size() - 1; i >= 4; --i) {
		unsigned int division = i;
		while (factor_table[division].first == factor_table[i].first) {
			division = factor_table[division].second;
		}
		factor_table[i].second = division;
	}
}

void factor(unsigned int num, vector<unsigned int>& factors) {
	// note: factors may be non-empty
	assert(num<factor_table.size());
	do {
		factors.push_back(factor_table[num].first);
		num = factor_table[num].second;
	} while (num != 1);
}

int parseLine(char* line) {
	int i = strlen(line);
	while (*line < '0' || *line > '9')
		line++;
	line[i - 3] = '\0';
	i = atoi(line);
	return i;
}

unsigned int getVirtualValue(unsigned int nrComps, unsigned int maxLength) { //Note: this value is in MB!
	FILE* file = fopen("/proc/self/status", "r");
	if (file == NULL) {
		// unable to obtain data, return an experimentally verified estimation...
		return nrComps * maxLength / (double) 10000.0;
	}
	unsigned result = 0;
	char line[128];

	while (fgets(line, 128, file) != NULL) {
		if (strncmp(line, "VmSize:", 7) == 0) {
			result = parseLine(line);
			break;
		}
	}
	fclose(file);
	return result / 1000;
}

unsigned int getPhysicalValue(unsigned int nrComps, unsigned int maxLength) { //Note: this value is in MB!
	FILE* file = fopen("/proc/self/status", "r");
	if (file == NULL) {
		// unable to obtain data, return an experimentally verified estimation...
		return nrComps * maxLength / (double) 10000.0;
	}
	unsigned result = 0;
	char line[128];

	while (fgets(line, 128, file) != NULL) {
		if (strncmp(line, "VmRSS:", 6) == 0) {
			result = parseLine(line);
			break;
		}
	}
	fclose(file);
	return result / 1000;
}

} /* namespace sym */
