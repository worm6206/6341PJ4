// Kevin Yen Jan 24
#include "scanner.h"
#include <sstream>

#define TEOF "EOF"
#define OpenParenthesis "OpenParenthesis"
#define ClosingParenthesis "ClosingParenthesis"
#define Atom "Atom"
#define ERROR "ERROR"

using namespace std;

void Scanner::Init(){
	string buff;
	while (getline(cin, buff)){
		InputLine+=buff + "\n";
	}
	Current = getNextToken();
}

void Scanner::MoveToNext(){
	Current = getNextToken(); 
}

// "index" is the starting position to get token
// "inputLines" is the string this function is reading
// "error" is for error message. Stays empty unless error occurs.
//  "atoms" is a string vector storing all literal atoms.
//  "sum" is for summing up all numeric atoms.
Token Scanner::getNextToken(){
	while (InputLine[Index]==32 || InputLine[Index]==9 || InputLine[Index]==13 || InputLine[Index]==10){
		Index++;
	}
	if((InputLine.length())==(unsigned)Index){
		return Token(TEOF);
	}
	else if(InputLine[Index]==40){
		Index++;
		return Token(OpenParenthesis,"(");
	}
	else if(InputLine[Index]==41){
		Index++;
		return Token(ClosingParenthesis,")");
	}
	else if((InputLine[Index]>=65) && (InputLine[Index]<=90)){
		string word = string(1,InputLine[Index]);
		int temp = Index;
		while( ((InputLine[++temp])>=65 && (InputLine[temp])<=90) || ((InputLine[temp])>=48 && (InputLine[temp])<=57) )
			word+=InputLine[temp];
		Index=temp;
		// atoms.push_back(word);
		return Token(Atom,word);
	}
	else if((InputLine[Index]>=48) && (InputLine[Index]<=57)){
		string number = string(1,InputLine[Index]);
		int temp = Index;
		while(((InputLine[++temp])>=65 && (InputLine[temp])<=90) || ((InputLine[temp])>=48 && (InputLine[temp])<=57) )
			number+=InputLine[temp];
		Index = temp;
		for(unsigned int i =0;i<number.length();i++){
			if (number[i] >=65 && number[i] <=90){
				error = "Invalid token " + number;
				return Token(ERROR);
			}
		}
		// sum+=stoi(number);
		return Token(Atom,number);
	}
	else{
		stringstream convert;
		convert << Index+1;
		error="unrecognized character \"" + string(1,InputLine[Index]) + "\" at " + convert.str();
		return Token(ERROR);
	}
}

void Scanner::print(stringstream& ss){
	ss << Current.Content;
}