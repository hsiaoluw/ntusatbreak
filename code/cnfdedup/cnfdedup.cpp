//============================================================================
// Name        : cnfdedup.cpp
// Author      : Jo Devriendt
// Version     : 1
// Copyright   : None, totally free!
// Description : Removes duplicate clauses and tautologies from a cnf file.
//============================================================================

#include <string>
#include <vector>
#include <set>
#include <unordered_set>
#include <algorithm>
#include <fstream>
#include <sstream>
#include <cmath>
#include <iterator>
#include <iostream>

using namespace std;

struct ClauseHash {
	size_t operator()(const vector<int>* first) const {
		unsigned int result = first->size();
		for (auto lit : *first) {
			result += abs(lit);
		}
		return (size_t) result;
	}
};

struct ClauseEqual {
	bool operator()(const vector<int>* first, const vector<int>* second) const {
		if (first->size() != second->size()) {
			return false;
		}
		for (unsigned int k = 0; k < first->size(); ++k) {
			// NOTE: clauses are sorted!
			if (first->at(k) != second->at(k)) {
				return false;
			}
		}
		return true;
	}
};

unordered_set<vector<int>*, ClauseHash, ClauseEqual> clauses;

void readCnf(string& filename) {
	ifstream file(filename);
	if (file) {
		string line;
		while (getline(file, line)) {
			if (line.front() == 'c') {
				// do nothing, this is a comment line
			} else if (line.front() == 'p') {
				// still do nothing, since we will check nVars and nClauses ourselves
			} else {
				istringstream is(line);
				set<int> tmpset = set<int>(istream_iterator<int>(is), istream_iterator<int>());
				bool isTautology = false;
				set<int> testset = set<int>();
				for (auto lit : tmpset) {
					isTautology = not testset.insert(abs(lit)).second;
					if(isTautology){
						break;
					}
				}
				// TODO: fix the case where clauses are spread over multiple lines
				// TODO: fix the case where lines contain multiple clauses
				if (not isTautology && tmpset.size()>0) {
					vector<int>* tmpvec = new vector<int>();
					for (auto lit : tmpset) {
						if(lit!=0){
							tmpvec->push_back(lit);
						}
					}
					clauses.insert(tmpvec);
				} // else clause was trivially satisfied!
			}
		}
	}
}

unsigned int findNVars() {
	unsigned int tmp = 0;
	for (auto clause : clauses) {
		for (auto lit : *clause) {
			if (tmp < abs(lit)) {
				tmp = abs(lit);
			}
		}
	}
	return tmp;
}

int main(int argc, char *argv[]) {
	//if (argc != 2) {
	//	cerr << "c Incorrect amount of arguments, shutting down...\n";
	//	return 1;
	//}
	unsigned int nVars;

	string filename = argv[1];
	readCnf(filename);
	nVars = findNVars();

	//string outfilename =argv[2];
	//ofstream outFile;
	//outFile.open(outFileName);
	
	cout << "p cnf " << nVars << " " << clauses.size() << "\n";
	for (auto clause : clauses) {
		for (auto lit : *clause) {
			cout << lit << " ";
		}
		cout << "0\n";
	}
	//outFile.close();
	return 0;
}
