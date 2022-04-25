//============================================================================
// Name        : Main.cpp
// Author      : Jo Devriendt
// Version     :
// Copyright   : 
// Description : Hello World in C, Ansi-style
//============================================================================
#include "Tools.h"
#include "Symmetry.h"
#include "SymmetryGroup.h"
#include "Translator.h"
#include <fstream>

using namespace std;
using namespace sym;

int main(int argc, char *argv[]) {
	//assert(false);
	string cnfFile;
	string symFile;
	string symExtension = ".sym";
	string outFile;
	if (argc < 3) {
		cout << "c ERROR: wrong number of arguments: " << argc << "\n";
		cout << "c At least two arguments expected: <cnfFile> <outFile> [verbosity]\n" << "The symmetry file is assumed to be <cnfFile>.sym";
		return 1;
	} else {
		cnfFile = argv[1];
		symFile = cnfFile + symExtension;
		outFile = argv[2];
		if (argc == 6) {
			maxMemory = atoi(argv[3]);
			maxTime = atoi(argv[4]);
			verbosity = atoi(argv[5]);
		} else if (argc == 5) {
			maxMemory = atoi(argv[3]);
			maxTime = atoi(argv[4]);
			verbosity = 0;
		} else if (argc == 4) {
			maxMemory = atoi(argv[3]);
			maxTime = 100;
			verbosity = 0;
		} else {
			maxMemory = 2000;
			maxTime = 100;
			verbosity = 0;
		}
	}

	if (verbosity > 0) {
		cout << "Reading in data... \n";
	}
	shared_ptr<Translator> trans = readCNF(cnfFile, outFile);
	vector<shared_ptr<SymmetryGroup> > groups;
	readSymmetries(symFile, trans, groups);
	nrSymGroups = groups.size();

	if (verbosity > 0) {
		cout << "c Number of symmetry groups detected: " << groups.size() << "\n";
		cout << "c Starting calculation... \n";
	}

	unsigned int ind = 0;
	for (auto group : groups) {
		group->checkForRelatedSyms(ind);
		group->eraseEmbeddedSyms();
		group->constructSymBreakingFormula();
		++ind;
	}

	trans->write();

	cout << "c BreakID ended succesfully :)\n" << flush;

//TODO: get this working

//	auto v = make_shared<vector<unsigned int> >();
//	for(unsigned int i=0; i<10; ++i){
//		v->push_back(i*i);
//	}
//	for(unsigned int i=0; i<3; ++i){
//		remove(v,(2+i*3));
//	}
//	for(unsigned int i=0; i<v->size(); ++i){
//		cout << v->at(i) << "+";
//	}

	return 0;
}
