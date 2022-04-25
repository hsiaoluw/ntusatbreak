/*
 * Tools.h
 *
 *  Created on: Jan 23, 2013
 *      Author: jodv
 */

#ifndef TOOLS_H_
#define TOOLS_H_

//#define NDEBUG

#include <string>
#include <vector>
#include <set>
#include <unordered_set>
#include <map>
#include <unordered_map>
#include <cmath>
#include <memory>
#include <sstream>
#include <iostream>
#include <assert.h> // TODO: is dit goed? Een .h ...
#include <climits>
#include <ctime>

using namespace std;

namespace sym {

class Symmetry;
class SymmetryGroup;
class Translator;

extern unsigned int verbosity;
extern unsigned int maxMemory; // in MiB
extern unsigned int maxTime; // in seconds
extern double usedTime;
extern unsigned int nrSymGroups;

int dimacs2lit(int);

int lit2dimacs(int);

vector<string> &split(const string&, char, vector<string>&);

vector<string> split(const string&, char);

shared_ptr<vector<int> > parseCycle(const string&);

void parseSymmetry(string& line, shared_ptr<map<int, int> > values);

bool commutesWithNegation(shared_ptr<map<unsigned int, int> > sym);

void readSymmetries(string& path, shared_ptr<Translator> trans, vector<shared_ptr<SymmetryGroup> >& symGroups);

shared_ptr<Translator> readCNF(string&, string&);

bool compareSymmetry(shared_ptr<Symmetry>, shared_ptr<Symmetry>);

template<typename T>
void remove(shared_ptr<vector<T> > list, unsigned int index) {
	(*list)[index] = list->back();
	list->pop_back();
}

// TODO: optimize with bitwise operators?
inline
bool sign(int lit) {
	return lit < 0;
}

inline
int neg(int lit) {
	return -lit;
}

inline
unsigned int prev(unsigned int lit) {
	return --lit;
}

inline
unsigned int next(unsigned int lit) {
	return ++lit;
}

inline
int commute(int key, int value) { // use the "commutes with negation" property.
	return (key > 0 ? value : -value);
}

inline
unsigned int pos(int lit) { // get the unsigned int positive value...
	return abs(lit);
}

bool areIndependent(shared_ptr<map<unsigned int, int> > sym1, shared_ptr<map<unsigned int, int> > sym2);

void removeOverlappingSyms(unordered_set<int>& lits, vector<shared_ptr<Symmetry> >& syms);

void fill_sieve(unsigned int n);
void factor(unsigned int num, vector<unsigned int>& factors);

unsigned int getVirtualValue(unsigned int nrComps, unsigned int maxLength); //Note: this value is in MB!
unsigned int getPhysicalValue(unsigned int nrComps, unsigned int maxLength); //Note: this value is in MB!

} /* namespace sym */

#endif /* TOOLS_H_ */
