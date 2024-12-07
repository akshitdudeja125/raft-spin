#define MAX_TERM 3// 1 to 3  
#define MAX_LOG 2// 0 to 1  
#define MAX_SERVER 3// 1 to 3  
#define NIL 10// a number that won't be used  

// message channels  
typedef AppendEntry {  
	byte term,leaderCommit,index,prevLogTerm  
};
typedef AppendEntryChannels {  
chan ch[MAX_SERVER] = [1] of { AppendEntry }  
};
AppendEntryChannels appendEntryChannels[MAX_SERVER];

typedef AppendEntryResponse {  
	byte term;
	bool success  
};
typedef AppendEntryResponseChannels {  
chan ch[MAX_SERVER] = [1] of { AppendEntryResponse }  
};
AppendEntryResponseChannels appendEntryResponseChannels[MAX_SERVER];

typedef RequestVote {  
	byte term,lastLogIndex,lastLogTerm  
};
typedef RequestVoteChannels {  
chan ch[MAX_SERVER] = [1] of { RequestVote }  
};
RequestVoteChannels requestVoteChannels[MAX_SERVER];

typedef RequestVoteResponse {  
	byte term;
	bool voteGranted  
};
typedef RequestVoteResponseChannels {  
chan ch[MAX_SERVER] = [1] of { RequestVoteResponse }  
};
RequestVoteResponseChannels requestVoteResponse_ch[MAX_SERVER];

// The following variables are actually local,  
// we move them globally, because SPIN doesn't support  
// that represent LTL with local variables.  
mtype: State = { leader,candidate,follower };
mtype: State state[MAX_SERVER];
byte currentTerm[MAX_SERVER];
typedef Logs {  
	byte logs[MAX_LOG]  
};
Logs logs[MAX_SERVER];
byte commitIndex[MAX_SERVER];

proctype server(byte serverId) {  
	state[serverId] = follower;
	byte votedFor = NIL;
	
// helpers  
	byte i;
	bool votesGranted[MAX_SERVER];
	RequestVote requestVote;
	byte lastLogTerm,lastLogIndex;
	RequestVoteResponse requestVoteResponse;
	bool logOk;
	
	AppendEntry appendEntry;
	AppendEntryResponse appendEntryResponse;
	
	do// main loop  
:: // timeout  
	(state[serverId] == candidate || state[serverId] == follower) -> 
	atomic {  
		state[serverId] = candidate;
		currentTerm[serverId] = currentTerm[serverId] + 1;
		
		end_max_term:  
		if// end if the limit is reached  
	:: (currentTerm[serverId] <= MAX_TERM) -> skip  
	fi  
	
	votedFor = serverId;
	do  
	:: i < MAX_SERVER -> 
		votesGranted[i] = 0;
		i++
	:: else -> break  
	od  
	votesGranted[serverId] = 1;
}  
:: // restart  
state[serverId] = follower  
:: // request vote  
(state[serverId] == candidate) -> 
atomic {  
	requestVote.term = currentTerm[serverId];
	if  
	:: (logs[serverId].logs[0] == 0) -> 
		requestVote.lastLogTerm = 0;
		requestVote.lastLogIndex = 0  
	:: (logs[serverId].logs[0] != 0 && logs[serverId].logs[1] == 0) -> 
		requestVote.lastLogTerm = logs[serverId].logs[0];
		requestVote.lastLogIndex = 1  
	:: (logs[serverId].logs[0] != 0 && logs[serverId].logs[1] != 0) -> 
		requestVote.lastLogTerm = logs[serverId].logs[1];
		requestVote.lastLogIndex = 2  
	fi  
	
	do  
	:: i < MAX_SERVER && serverId != i -> 
		requestVoteChannels[serverId].ch[i]!requestVote;
		i++
	:: else -> break  
	od  
}  
:: // become leader  
(state[serverId] == candidate && (votesGranted[0] + votesGranted[1] + votesGranted[2] > 1)) -> 
state[serverId] = leader  
:: // handle RequestVote  
(requestVoteChannels[0].ch[serverId]?[requestVote] || requestVoteChannels[1].ch[serverId]?[requestVote] || requestVoteChannels[2].ch[serverId]?[requestVote]) -> 
atomic {  
// calculate the id of the sender  
	if  
	:: requestVoteChannels[0].ch[serverId]?requestVote -> i = 0  
	:: requestVoteChannels[1].ch[serverId]?requestVote -> i = 1  
	:: requestVoteChannels[2].ch[serverId]?requestVote -> i = 2  
	fi  
	assert(i != serverId);
	
// update terms  
	if  
	:: (requestVote.term > currentTerm[serverId]) -> 
		currentTerm[serverId] = requestVote.term;
		state[serverId] = follower;
		votedFor = NIL  
	:: (requestVote.term <= currentTerm[serverId]) -> 
		skip  
	fi  
	
	if  
	:: (logs[serverId].logs[0] == 0) -> 
		lastLogTerm = 0;
		lastLogIndex = 0  
	:: (logs[serverId].logs[0] != 0 && logs[serverId].logs[1] == 0) -> 
		lastLogTerm = logs[serverId].logs[0];
		lastLogIndex = 1  
	:: (logs[serverId].logs[0] != 0 && logs[serverId].logs[1] != 0) -> 
		lastLogTerm = logs[serverId].logs[1];
		lastLogIndex = 2  
	fi  
	
	logOk = requestVote.lastLogTerm > lastLogTerm || requestVote.lastLogTerm == lastLogTerm && requestVote.lastLogIndex >= lastLogIndex;
	requestVoteResponse.voteGranted = requestVote.term == currentTerm[serverId] && logOk && (votedFor == NIL || votedFor == i);
	requestVoteResponse.term = currentTerm[serverId];
	
	if  
	:: requestVoteResponse.voteGranted -> votedFor = i  
	:: !requestVoteResponse.voteGranted -> skip  
	fi  
	requestVoteResponse_ch[serverId].ch[i]!requestVoteResponse;
}  
:: // handle RequestVoteResponse  
(requestVoteResponse_ch[0].ch[serverId]?[requestVoteResponse] || requestVoteResponse_ch[1].ch[serverId]?[requestVoteResponse] || requestVoteResponse_ch[2].ch[serverId]?[requestVoteResponse]) -> 
atomic {  
// calculate the id of the sender  
	if  
	:: requestVoteResponse_ch[0].ch[serverId]?requestVoteResponse -> i = 0  
	:: requestVoteResponse_ch[1].ch[serverId]?requestVoteResponse -> i = 1  
	:: requestVoteResponse_ch[2].ch[serverId]?requestVoteResponse -> i = 2  
	fi  
	assert(i != serverId);
	
	if  
	:: (requestVoteResponse.term > currentTerm[serverId]) -> // update terms  
		currentTerm[serverId] = requestVoteResponse.term;
		state[serverId] = follower;
		votedFor = NIL  
	:: (requestVoteResponse.term == currentTerm[serverId] && requestVoteResponse.voteGranted) -> 
		votesGranted[i] = 1  
	:: !(requestVoteResponse.term > currentTerm[serverId]) && !(requestVoteResponse.term == currentTerm[serverId] && requestVoteResponse.voteGranted) -> 
		skip  
	fi  
}  
:: // append entries  
(state[serverId] == leader) -> 
atomic {  
	do  
	:: i < MAX_SERVER && serverId != i -> 
		appendEntry.term = currentTerm[serverId];
		appendEntry.leaderCommit = commitIndex[serverId];
		if  
		:: (logs[serverId].logs[0] != logs[i].logs[0]) -> 
			appendEntry.index = 0  
		:: (logs[serverId].logs[1] != 0 && logs[serverId].logs[0] == logs[i].logs[0] && logs[serverId].logs[1] != logs[i].logs[1]) -> 
			appendEntry.index = 1  
			appendEntry.prevLogTerm = logs[i].logs[0]  
		:: appendEntry.index = NIL  
		fi  
		appendEntryChannels[serverId].ch[i]!appendEntry;
		i++
	:: else -> break  
	od  
}  
:: // handle AppendEntry  
(appendEntryChannels[0].ch[serverId]?[appendEntry] || appendEntryChannels[1].ch[serverId]?[appendEntry] || appendEntryChannels[2].ch[serverId]?[appendEntry]) -> 
atomic {  
// calculate the id of the sender  
	if  
	:: appendEntryChannels[0].ch[serverId]?appendEntry -> i = 0  
	:: appendEntryChannels[1].ch[serverId]?appendEntry -> i = 1  
	:: appendEntryChannels[2].ch[serverId]?appendEntry -> i = 2  
	fi  
	assert(i != serverId);
	
// update terms  
	if  
	:: (appendEntry.term > currentTerm[serverId]) -> 
		currentTerm[serverId] = appendEntry.term;
		state[serverId] = follower;
		votedFor = NIL  
	:: (appendEntry.term <= currentTerm[serverId]) -> 
		skip  
	fi  
	assert(appendEntry.term <= currentTerm[serverId]);
	
// return to follower state  
	if  
	:: (appendEntry.term == currentTerm[serverId] && state[serverId] == candidate) -> 
		state[serverId] = follower;
		votedFor = NIL  
	:: (appendEntry.term != currentTerm[serverId] || state[serverId] != candidate) -> 
		skip  
	fi  
	assert(!(appendEntry.term == currentTerm[serverId]) || (state[serverId] == follower));
	
	logOk = appendEntry.index == 0 || (appendEntry.index == 1 && appendEntry.prevLogTerm == logs[serverId].logs[0]);
	appendEntryResponse.term = currentTerm[serverId];
	
	if  
	:: (appendEntry.term < currentTerm[i] || appendEntry.term == currentTerm[serverId] && state[serverId] == follower && !logOk) -> // reject request  
		appendEntryResponse.success = 0;
		appendEntryResponseChannels[serverId].ch[i]!appendEntryResponse  
	:: (appendEntry.term == currentTerm[serverId] && state[serverId] == follower && logOk) -> 
		appendEntryResponse.success = 1;
		logs[serverId].logs[appendEntry.index] = appendEntry.term;
		commitIndex[serverId] = appendEntry.leaderCommit;
		appendEntryResponseChannels[serverId].ch[i]!appendEntryResponse  
	fi  
}  
:: // handle AppendEntryResponse  
(appendEntryResponseChannels[0].ch[serverId]?[appendEntryResponse] || appendEntryResponseChannels[1].ch[serverId]?[appendEntryResponse] || appendEntryResponseChannels[2].ch[serverId]?[appendEntryResponse]) -> 
atomic {  
// calculate the id of the sender  
	if  
	:: appendEntryResponseChannels[0].ch[serverId]?appendEntryResponse -> i = 0  
	:: appendEntryResponseChannels[1].ch[serverId]?appendEntryResponse -> i = 1  
	:: appendEntryResponseChannels[2].ch[serverId]?appendEntryResponse -> i = 2  
	fi  
	assert(i != serverId);
	
	if  
	:: (appendEntryResponse.term > currentTerm[serverId]) -> // update terms  
		currentTerm[serverId] = appendEntryResponse.term;
		state[serverId] = follower;
		votedFor = NIL  
	:: (appendEntryResponse.term < currentTerm[serverId]) -> 
		skip  
	:: (appendEntryResponse.term == currentTerm[serverId] && appendEntryResponse.success && state[serverId] == leader) -> // advance commit index  
// as we only have 3 servers  
// one success AppendEntry means committed  
		if  
		:: (commitIndex[serverId] == 0 && logs[i].logs[0] == logs[serverId].logs[0]) -> 
			commitIndex[serverId] = 1  
		:: (commitIndex[serverId] == 1 && !(logs[serverId].logs[1] != 0 && logs[i].logs[1] == logs[serverId].logs[1])) -> 
			skip;// actually this case won't be reached  
		fi  
	:: (appendEntryResponse.term == currentTerm[serverId] && !(appendEntryResponse.success && state[serverId] == leader)) -> 
		skip  
	fi  
}  
:: // client request  
(state[serverId] == leader && logs[serverId].logs[1] == 0) -> 
if  
:: logs[serverId].logs[0] == 0 -> logs[serverId].logs[0] = currentTerm[serverId]  
:: logs[serverId].logs[0] != 0 -> logs[serverId].logs[1] = currentTerm[serverId]  
fi  
od  
}  

init {  
// run server(0);
// run server(1);
// run server(2);
byte i = 0;
do
:: i < MAX_SERVER -> run server(i);i++
:: else -> break
od

}  
// end of file raft1.pml