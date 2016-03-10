// Kevin Yen Jan 24
#include <string>
#include <iostream>
#include <sstream>

#ifndef SCANNER_H
#define SCANNER_H

using namespace std;

// Count stuff
struct Counter{ // Not used at all in project 2. But might be usefull after this project, so kept it.
	int LiteralAtom, numericAtom, openPar, closingPar, sum, index;
	Counter() : LiteralAtom(0), numericAtom(0), openPar(0), closingPar(0), sum(0), index(0) {}
};

struct Token{ // a Token consists a Type and Content. Example: Type: Atom, Content: 123.
	string Type, Content;
	Token(string a, string b){
		Type = a;
		Content = b;
	}
	Token(string a){
		Type = Content = a;
	}
	Token(){}
};

// Scan stuff return token
// This is from last project, modified a little bit to fit in.
struct Scanner{
	int Index;
	string InputLine, error;
	Token Current;
	void Init();// read file
	void MoveToNext();
	Token getNextToken();
	void print(stringstream& ss);
};

#endif