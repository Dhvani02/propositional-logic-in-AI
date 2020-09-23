#include <bits/stdc++.h>
#include <unordered_map>
#include <unordered_set>
using namespace std;
class ResolutionProof{

typedef vector<string> arguments;
	static bool isVariable(const string &x) {
		return islower(x[0]);
	}

struct predicate {
	bool negated;
	string name;
	arguments args;
	  bool operator==(const predicate &p) const {
      size_t this_sent = 17;
			this_sent += hash<string>()(this->name);
      this_sent += hash<bool>()(this->negated);
			for (int i = 0; i < this->args.size(); i++) {
				if (!(isVariable(this->args[i])))
          this_sent += hash<string>()(this->args[i]);
				else
					this_sent += hash<string>()("x");
			}

			size_t compare_sent = 17;
			compare_sent += hash<string>()(p.name);
      compare_sent += hash<bool>()(p.negated);
			
			for (int i = 0; i < p.args.size(); i++) {
				if (!(isVariable(p.args[i])))
					compare_sent += hash<string>()(p.args[i]);
				else
					compare_sent += hash<string>()("x");
			}

			return this_sent == compare_sent;
		}


	predicate (string &s){
		if(s[0] == '~')
			negated = true;
		else
			negated = false;
		//name
		unsigned int j = 0;
		while(s[j++] != '(');
		if (negated)
			name = s.substr(1, j-2);
		else
			name = s.substr(0, j-1);
		//args
		for(unsigned int i = j; i < s.length(); i++){
			if(s[i] == ')' || s[i] == ','){
				args.push_back(s.substr(j, i-j));
				j = i + 1;
			}
		}
	}
	predicate negate() {
			bool flag = !negated;
			string value = name;
			arguments a = args;
			return predicate(flag, value, a);
		}
	predicate(bool &flag, string &value, arguments &a) {
		negated = flag;
		name = value;
		args = a;
	}

};

typedef vector<predicate> clause;

struct predicate_sort
{
    bool operator()(predicate const & a, predicate const & b) const
    {
        if (a.name != b.name)
          return a.name < b.name;
        return a.args[0] < b.args[0];
    }
};
//citation: https://stackoverflow.com/questions/19195183/how-to-properly-hash-the-custom-struct.
struct hash_clause {
  bool VERBOSE = false;
		size_t operator()(const clause &s) const {
			int variable_count = 0;
			unordered_map<string, int> visited_variables;

			if (VERBOSE) {
				cout << "System debugg: Print debbugging values\n";
			}

			size_t signature = 0;
			for (int i = 0; i < s.size(); i++) {
				size_t temp = 17;
        temp +=  hash<string>()(s[i].name);
				temp +=  hash<bool>()(s[i].negated);
				for (int j = 0; j < s[i].args.size(); j++) {
					if (isVariable(s[i].args[j])) {
						if (visited_variables.count(s[i].args[j]) == 0) {
							variable_count++;
							visited_variables[s[i].args[j]] = variable_count;
						}
						temp += hash<int>()(visited_variables[s[i].args[j]]);
					} else {
						temp += hash<string>()(s[i].args[j]);
					}
				}
				signature ^= temp;
			}
			return signature;
		}
	};


clause negateAlpha(clause &s){
for(int i = 0; i < s.size(); i++){
		s[i] = s[i].negate();

	}
	return s;
}
//*************************************************************************************************************
class KnowledgeBase{
public:
	static bool isVariable(const char &x) {
		return islower(x);
	}
	

public:
	unordered_map<char, unsigned int> variables; 
	vector<clause> data; 
	unordered_map<string, vector<pair<unsigned int, unsigned int> > >KBmap; 
	KnowledgeBase copy(){
		KnowledgeBase temp;
		temp.data = this->data;
		temp.variables = this->variables;
		temp.KBmap = this->KBmap;
		return temp;
	}

clause standardize(clause &s){
	unordered_set<char> current_vars;
    int i = 0;
		while(i < s.size()){
			arguments &arg = s[i].args;
      		int j = 0;
			while(j < arg.size()){
				char var = arg[j][0];
				if(isVariable(var)){
					if(current_vars.find(var) == current_vars.end()){
						if(variables.find(var) == variables.end()){
							variables[var] = 1;
						}
						else
							variables[var]++;
					current_vars.insert(var);
					}
					//cout << arg[j] << " ";
					arg[j] = var+to_string(variables[var]);
				}
        	j++;
			}
      i++;
	}
	return s;
}

	

void printSent(clause &s){
	for(int i = 0; i < s.size(); i++){
		if(s[i].negated)
			cout << "~";
		cout << s[i].name << "(";
		for(int j = 0; j < s[i].args.size(); j++){
			cout << s[i].args[j] << ",";
		}
		cout << ")\t";
	}
	cout <<endl;
}
	void store(clause &s){
		s = standardize(s);

		data.push_back(s);
		unsigned int loc = data.size()-1;
		for(int i = 0; i < s.size(); i++){ 
			if(!s[i].negated){
				KBmap[s[i].name].push_back(make_pair(loc,i));
			}
			else{
				KBmap['~'+s[i].name].push_back(make_pair(loc,i));
			}
		}


	}
	vector<pair<clause, unsigned int> > getKBMap(predicate &p){
		vector<pair<clause, unsigned int> > result;
		vector<pair<unsigned int, unsigned int> > resolvableSentsLoc;
		resolvableSentsLoc = KBmap[p.name];
		for(int i = 0; i < resolvableSentsLoc.size(); i++){
			result.push_back(make_pair(data[resolvableSentsLoc[i].first], resolvableSentsLoc[i].second));
		}
		return result;
	}
};


//*************************************************************************************************************


static string convertToString(predicate &s){
	string r="";
			if(s.negated)
				r = '~'+r;
			r = r + s.name + '#';
			for(int j = 0; j < s.args.size(); j++){
				r = r + s.args[j] + '#';
			}
			return r;
		}

clause makeUnique(clause &s){
	unordered_set<string> visited;
	unordered_map<string, int> visited_2;
	vector<int> to_remove;
	vector<int> to_remove_2;
	for(int i = 0; i < s.size(); i++){
		string r = convertToString(s[i]);
		if(visited.count(r) == 0)
			visited.insert(r);
		else
			to_remove.push_back(i);
	}
	for(int i = 0; i < to_remove.size(); i++){
		s.erase(s.begin() + to_remove[i]);
	}
return s;
for(int i = 0; i < s.size(); i++){
		string actual = convertToString(s[i]);
		if(!s[i].negated){
			string check = '~'+actual;
			if(visited_2.count(check) == 0)
				visited_2[actual] = i;
			else{
				to_remove.push_back(i);
				to_remove.push_back(visited_2[check]);
			}
		}
		else if(s[i].negated){
			string check = actual.substr(1);
			if(visited_2.count(check) == 0)
				visited_2[actual] = i;
			else{
				to_remove_2.push_back(i);
				to_remove_2.push_back(visited_2[check]);
			}
		}
	}
	
}
// //*************************************************************************************************************

void printSent(clause &s){
	for(int i = 0; i < s.size(); i++){
		if(s[i].negated)
			cout << "~";
		cout << s[i].name << "(";
		for(int j = 0; j < s[i].args.size(); j++){
			cout << s[i].args[j] << ",";
		}
		cout << ")\t";
	}
	cout <<endl;
}

vector<string> tokenise(string s, size_t f){
	vector<string> ans;
	s.erase(remove_if(s.begin(), s.end(), ::isspace), s.end());

	for(int i = 0; i < s.size(); i++){
		if(s[i] != '&' && s[i] != '|' && s[i] != '=' && s[i] != '>'){
			int j = i;
			while(s[j] != ')')j++;
			if(j < f){
				//cout << i << " " << f << endl;
				if(s.substr(i, j-i+1)[0] == '~')
					ans.push_back(s.substr(i+1, j-i+1));
				else
					ans.push_back('~'+s.substr(i, j-i+1));
			}
			else
				ans.push_back(s.substr(i, j-i+1));
			i=j;
		}
		else
			continue;
	}
	return ans;
}
vector<clause> preprocess_input(vector<string> s){
	vector<clause> result;
	vector<predicate> preds;
	for(int i = 0; i < s.size(); i++){
		preds.clear();
		if(s[i].find("=>") == string::npos){
			predicate p = predicate(s[i]);
			preds.push_back(p);
			result.push_back(preds);
		}
		else{
			size_t f = s[i].find("=>");
			vector<string> tokens = tokenise(s[i],f);
			for(int j = 0; j < tokens.size(); j++){
				predicate p = predicate(tokens[j]);
				preds.push_back(p);
			}
			result.push_back(preds);
		}
	}
	return result;
}
public:
KnowledgeBase db;

void tell(vector<string> &s){
	vector<clause> clauses = preprocess_input(s);
	for(int i = 0; i < clauses.size(); i++){
		//printSent(clauses[i]);
		db.store(clauses[i]);
	}
}


arguments &substitute(arguments &x, unordered_map<string, string> &theta) {
		for (int i = 0; i < x.size(); i++) {
			while (theta.find(x[i]) != theta.end())
				x[i] = theta[x[i]];
		}
		return x;
	}

	bool unify(arguments &x, arguments &y, unordered_map<string, string> &theta) {
		if (x.size() != y.size())
			return false;
		for (int i = 0; i < x.size(); i++) {
			if (x[i] != y[i]) {
				if (isVariable(x[i])) {
					theta[x[i]] = y[i];
					x = substitute(x,theta);
					y = substitute(y,theta);
				} else if (isVariable(y[i])) {
					theta[y[i]] = x[i];
					x = substitute(x,theta);
					y = substitute(y,theta);
				} else {
					//If x[i] and y[i] both are constants
					return false;
				}
			}
		}
		return true;
	}
////////////////////////
clause select_random_branch(){
	int current_count = 0;
	for(int i = 0; i < db.data.size(); i++){
		current_count = rand()%3;
		if(rand()%3 == 0){
			return db.data[current_count];
		}
	}
	set <string> new_branch;
	clause s1;
	for(int i = 0; i < db.data.size(); i++){
		string result = "";
		for(int j = 0; j < db.data[i].size();j++){
			string s = convertToString(db.data[i][j]);
			result = result.append(s);
		}
		new_branch.insert(result);
	}
	for(auto i : new_branch){
		string s = i;
		s = s + '#';

	}
	return s1;
  }
 clause convert_query_to_cnf(){
	int current_count = 0;
	for(int i = 0; i < db.data.size(); i++){
		current_count = rand()%3;
		if(rand()%3 == 0){
			return db.data[current_count];
		}
	}
	set <string> new_branch;
	clause s1;
	for(int i = 0; i < db.data.size(); i++){
		string result = "";
		for(int j = 0; j < db.data[i].size();j++){
			string s = convertToString(db.data[i][j]);
			result = result.append(s);
		}
		new_branch.insert(result);
	}
	for(auto i : new_branch){
		string s = i;
		s = s + '#';

	}
	return s1;
  }

string convertToString_loop_detector(predicate &s){
	string r="";
			if(s.negated)
				r = '~'+r;
			r = r + s.name + '#';
			for(int j = 0; j < s.args.size(); j++){
				if(isVariable(s.args[j])){
					r = r + 'x' + '#';
				}
				else{
					r = r + s.args[j] + '#';
				}
			}
			return r;
}
clause convert_to_set(clause s){
  clause result;
  unordered_set<string> unique;
  for(int i = 0; i < s.size(); i++){
      string r = "";
      if(s[i].negated){
        r = r + '~';
    }
      r = r + s[i].name + '#';
      for(int k = 0; k < s[i].args.size(); k++){
        r = r + s[i].args[k] + '#';
      }
    unique.insert(r);
  }
  for(auto i : unique){
    result.push_back(predicate(i));
  }
  return result;
}
  clause convert_query_new(){
	int current_count = 0;
	for(int i = 0; i < db.data.size(); i++){
		current_count = rand()%3;
		if(rand()%1 == 0){
			return db.data[current_count];
		}
	}
	set <string> new_branch;
	clause s1;
	for(int i = 0; i < db.data.size(); i++){
		string result = "";
		for(int j = 0; j < db.data[i].size();j++){
			string s = convertToString(db.data[i][j]);
			result = result.append(s);
		}
		new_branch.insert(result);
	}
	for(auto i : new_branch){
		string s = i;
		s = s + '#';

	}
	return s1;
  }
string hash_loop_detector_string(clause s){
sort(s.begin(), s.end(), predicate_sort());
	string result = "";
  for(int i = 0; i < s.size(); i++){
		string inter = convertToString_loop_detector(s[i]);
		result = result.append(inter);
		result = result + '#';
		}
		return result;
}
bool check_repeat(vector<clause> s){
  for(int i = 0; i < s.size(); i++){
    for(int j = i; j < s[i].size(); j++){
      if(s[i] == s[j])
        return false;
    }
  }
  return true;
}
string hash_loop_detector(clause &s){
	string r = "";
	unordered_map<string, int> already_visited;
	int v_count = 0;
	for(int i = 0; i < s.size(); i++){
		if(s[i].negated)
			r = r + '~';
		r = r + s[i].name + '#';
		for(int j = 0; j < s[i].args.size(); j++){
			if(isVariable(s[i].args[j])){
				if(already_visited.find(s[i].args[j]) == already_visited.end()){
					v_count++;
					already_visited[s[i].args[j]] = v_count;
				}
				r = r + s[i].args[j]+ to_string(already_visited[s[i].args[j]]) + '#';
			}
			else
				r = r + s[i].args[j] + '#';
		}
	}
	return r;
}
///////////////////////
// void printSent(clause &s){
// 	for(int i = 0; i < s.size(); i++){
// 		if(s[i].negated)
// 			cout << "~";
// 		cout << s[i].name << "(";
// 		for(int j = 0; j < s[i].args.size(); j++){
// 			cout << s[i].args[j] << ",";
// 		}
// 		cout << ")\t";
// 	}
// 	cout <<endl;
// }

clause mergeSent(clause lhs, clause rhs){
  clause result;
  for(auto i : lhs){
    result.push_back(i);
  }
  for(auto i : rhs){
    result.push_back(i);
  }
  return result;
  
}
clause preprocess_query(string s){
	vector<predicate> p;
  s.erase(remove_if(s.begin(), s.end(), ::isspace), s.end());
	predicate p1 = predicate(s);
	p.push_back(p1);
	return p;
}
bool ask(string &query){
	queue<clause> ResolutionQueue;
  clock_t finishtime = clock()+5000000;
	unordered_set<clause, hash_clause> LoopDetector; 

	clause alpha = preprocess_query(query);
  //cout << "alpha" ;
  //printSent(alpha);
  clause copy_alpha = alpha;
	clause notAlpha = negateAlpha(alpha);
  ResolutionQueue.push(notAlpha);

  KnowledgeBase kb = db.copy();
  kb.store(notAlpha);

	while(!ResolutionQueue.empty()){
   // cout << kb.KBmap["B"].size() << " ";
		clause currSent = ResolutionQueue.front();
		//cout << "curr sent: " ;printSent(currSent);
		ResolutionQueue.pop();
		for(int i = 0; i < currSent.size(); i++){
			predicate resolver = currSent[i].negate();
      //CHECK THIS
      if (resolver.negated)
        resolver.name = '~'+resolver.name;
      
			vector<pair<clause, unsigned int> > resolvableSents = kb.getKBMap(resolver);
      		//cout << resolvableSents.size();
			for(int j = 0; j < resolvableSents.size(); j++){
				unordered_map<string, string> theta;
						//cout << "resolving sent: " ; 
						//printSent(resolvableSents[j].first);

						arguments x = currSent[i].args;
						arguments y = resolvableSents[j].first[resolvableSents[j].second].args;
						if (unify(x, y, theta)) {
				
							clause left_side = currSent;
							clause right_side = resolvableSents[j].first;
              
							for (int k = 0; k < left_side.size(); k++){
								left_side[k].args = substitute(left_side[k].args, theta);
							}
							for (int k = 0; k < right_side.size(); k++){
								right_side[k].args = substitute(right_side[k].args, theta);
							}

							 //cout << "resolving sent: " ; printSent(resolvableSents[j].first);
							
							left_side.erase(left_side.begin() + i);
							right_side.erase(right_side.begin() + resolvableSents[j].second);

							clause resolvent = mergeSent(left_side, right_side);

							resolvent = makeUnique(resolvent);

							if (resolvent.empty()) {
								db.store(copy_alpha);
								//cout << "true";
								return true;
							}
							//string LoopDetectorString = hash_loop_detector(resolvent);
							if(LoopDetector.find(resolvent) == LoopDetector.end()){
								kb.store(resolvent);
								ResolutionQueue.push(resolvent);
								LoopDetector.insert(resolvent);
							}

						}
			}
			if(clock() > finishtime)
				return false;
		}
	}
return false;
}
};
int main(){
	ifstream fin("input.txt");
	ofstream myfile("output.txt");
	int n,q;
	string s;
	ResolutionProof kb;
	vector<string> queries;
	vector<string> knowledge;
	getline(fin,s);
	q = stoi(s);
	for(int i = 0; i < q; i++){
		getline(fin,s);
		queries.push_back(s);
	}
	getline(fin,s);
	n = stoi(s);
	for(int i = 0; i < n; i++){
		getline(fin,s);
		knowledge.push_back(s);
	}
	kb.tell(knowledge);

for(int i = 0; i < queries.size(); i++){
		if(kb.ask(queries[i])) {
			cout <<"true"<<endl;
      if(i != queries.size()-1)
			  myfile << "TRUE" <<endl;
        else
        myfile << "TRUE";
		}
		else{
			cout <<"false"<<endl;
      if(i != queries.size()-1)
			  myfile << "FALSE" <<endl;
        else
        myfile << "FALSE";
		}
	}
	myfile.close();
    
    cout << 1.0*clock()/CLOCKS_PER_SEC <<endl;

}
