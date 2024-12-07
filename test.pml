#define N 3// Number of servers,can be modified
#define MAX_TERM 3// 1 to any value
#define MAX_LOG 2// 0 to any value
#define NIL 10// a number that won't be used

// message channels
typedef AppendEntry {
	byte term,leaderCommit,index,prevLogTerm,senderId
};
chan appendEntryChannels[N] = [N] of { AppendEntry };// One channel per server

typedef AppendEntryResponse {
	byte term;
	bool success;
	byte senderId;
};
chan appendEntryResponseChannels[N] = [N] of { AppendEntryResponse };// One channel per server

typedef RequestVote {
	byte term,lastLogIndex,lastLogTerm,senderId
};
chan requestVoteChannels[N] = [N] of { RequestVote };// One channel per server

typedef RequestVoteResponse {
	byte term;
	bool voteGranted;
	byte senderId;
};
chan requestVoteResponseChannels[N] = [N] of { RequestVoteResponse };// One channel per server

mtype = { leader,candidate,follower };
mtype state[N];
byte currentTerm[N];
typedef Logs {
	byte log[MAX_LOG];
};
Logs log[N];
byte commitIndex[N];

// Helper functions
inline majority() {
	((N / 2) + 1)
}

proctype server(byte serverId) {
	state[serverId] = follower;
	byte votedFor = NIL;
	byte i;
	
	bool votesGranted[N];
	RequestVote requestVote;
	byte lastLogTerm,lastLogIndex;
	RequestVoteResponse rvr;
	bool logOk;
	
	AppendEntry ae;
	AppendEntryResponse aer;
	int voteCount;
	
	do// main loop
:: // timeout
	(state[serverId] == candidate || state[serverId] == follower) -> 
	atomic {
		state[serverId] = candidate;
		currentTerm[serverId] = currentTerm[serverId] + 1;
		
// Check if term exceeds MAX_TERM
		if
		:: (currentTerm[serverId] <= MAX_TERM) -> skip
		:: else -> break
		fi
		
		votedFor = serverId;
// Reset votesGranted
		i = 0;
		do
		:: (i < N) -> 
			votesGranted[i] = false;
			i++
		:: else -> break
		od
		votesGranted[serverId] = true;
	}
:: // restart
	state[serverId] = follower
:: // request vote
	(state[serverId] == candidate) -> 
	atomic {
		requestVote.term = currentTerm[serverId];
		requestVote.senderId = serverId;
// Determine last log term and index
		if
		:: (log[serverId].log[0] == 0) -> 
			requestVote.lastLogTerm = 0;
			requestVote.lastLogIndex = 0
		:: else -> 
			requestVote.lastLogTerm = log[serverId].log[MAX_LOG - 1];
			requestVote.lastLogIndex = MAX_LOG
		fi
		
// Send RequestVote to all other servers
		i = 0;
		do
		:: (i < N) -> 
			if
			:: (i != serverId) -> 
				requestVoteChannels[i]!requestVote
			fi;
			i++
		:: else -> break
		od
	}
:: // become leader
	(state[serverId] == candidate) -> 
// Count votes
	voteCount = 0;
	i = 0;
	do
	:: (i < N) -> 
		if
		:: votesGranted[i] -> voteCount++
		:: else -> skip
		fi;
		i++
	:: else -> break
	od;
	if
	:: (voteCount >= majority()) -> 
		state[serverId] = leader
	fi
:: // handle RequestVote
	(len(requestVoteChannels[serverId]) > 0) -> 
	requestVoteChannels[serverId]?requestVote;
	
	
	
	atomic {
		i = requestVote.senderId;
// update terms
		if
		:: (requestVote.term > currentTerm[serverId]) -> 
			currentTerm[serverId] = requestVote.term;
			state[serverId] = follower;
			votedFor = NIL
		:: else -> skip
		fi
		
// Determine last log term and index
		if
		:: (log[serverId].log[0] == 0) -> 
			lastLogTerm = 0;
			lastLogIndex = 0
		:: else -> 
			lastLogTerm = log[serverId].log[MAX_LOG - 1];
			lastLogIndex = MAX_LOG
		fi
		
		logOk = requestVote.lastLogTerm > lastLogTerm || (requestVote.lastLogTerm == lastLogTerm && requestVote.lastLogIndex >= lastLogIndex);
		rvr.voteGranted = (requestVote.term == currentTerm[serverId]) && logOk && (votedFor == NIL || votedFor == i);
		
		if
		:: rvr.voteGranted -> votedFor = i
		:: else -> skip
		fi
		rvr.term = currentTerm[serverId];
		rvr.senderId = serverId;
		requestVoteResponseChannels[i]!rvr
	}
:: // handle RequestVoteResponse
	(len(requestVoteResponseChannels[serverId]) > 0) -> 
	requestVoteResponseChannels[serverId]?rvr;
	atomic {
		i = rvr.senderId;
		if
		:: (rvr.term > currentTerm[serverId]) -> 
			currentTerm[serverId] = rvr.term;
			state[serverId] = follower;
			votedFor = NIL
		:: else -> 
			if
			:: (rvr.term == currentTerm[serverId] && rvr.voteGranted) -> 
				votesGranted[i] = true
			:: else -> skip
			fi
		fi
	}
	
:: // append entries
	(state[serverId] == leader) -> 
	atomic {
		ae.term = currentTerm[serverId];
		ae.leaderCommit = commitIndex[serverId];
		ae.senderId = serverId;
		
// Send AppendEntry to all other servers
		i = 0;
		do
		:: (i < N) -> 
			if
			:: (i != serverId) -> 
// Determine index and prevLogTerm
				if
				:: (log[serverId].log[0] != log[i].log[0]) -> 
					ae.index = 0
				:: (log[serverId].log[1] != 0 && log[serverId].log[0] == log[i].log[0] && log[serverId].log[1] != log[i].log[1]) -> 
					ae.index = 1;
					ae.prevLogTerm = log[i].log[0]
				:: else -> 
					ae.index = NIL
				fi
				appendEntryChannels[i]!ae
			fi;
			i++
		:: else -> break
		od
	}
:: // handle AppendEntry
	(len(appendEntryChannels[serverId]) > 0) -> 
	appendEntryChannels[serverId]?ae;
	atomic {
		i = ae.senderId;
// update terms
		if
		:: (ae.term > currentTerm[serverId]) -> 
			currentTerm[serverId] = ae.term;
			state[serverId] = follower;
			votedFor = NIL
		:: else -> skip
		fi
		
// return to follower state
		if
		:: (ae.term == currentTerm[serverId] && state[serverId] == candidate) -> 
			state[serverId] = follower;
			votedFor = NIL
		:: else -> skip
		fi
		
// Check logOk
		logOk = (ae.index == 0) || (ae.index == 1 && ae.prevLogTerm == log[serverId].log[0]);
		aer.term = currentTerm[serverId];
		aer.senderId = serverId;
		if
		:: (ae.term < currentTerm[serverId] || (ae.term == currentTerm[serverId] && state[serverId] == follower && !logOk)) -> 
			aer.success = false;
		:: else -> 
			aer.success = true;
			log[serverId].log[ae.index] = ae.term;
			commitIndex[serverId] = ae.leaderCommit;
		fi
:: 	}
:: // handle AppendEntryResponse
	(len(appendEntryResponseChannels[serverId]) > 0) -> 
	appendEntryResponseChannels[serverId]?aer;
	atomic {
		i = aer.senderId;
		if
		:: (aer.term > currentTerm[serverId]) -> 
			currentTerm[serverId] = aer.term;
			state[serverId] = follower;
			votedFor = NIL
		:: else -> 
			if
			:: (aer.term == currentTerm[serverId] && aer.success && state[serverId] == leader) -> 
// Track successful acknowledgments
// For simplicity, assume entries are committed when majority acknowledges
// You may need to maintain matchIndex array for accurate tracking
				commitIndex[serverId] = ae.leaderCommit
			:: else -> skip
			fi
		fi
	}
:: // client request
	(state[serverId] == leader && log[serverId].log[MAX_LOG - 1] == 0) -> 
	log[serverId].log[MAX_LOG - 1] = currentTerm[serverId]
od
};

init {
byte i;
i = 0;
do
:: (i < N) -> 
	run server(i);
	i++
:: else -> break
od
}

// LTL properties need to be adjusted to handle arbitrary N.
// For example, leader election safety can be formulated as:
// "At most one leader in a given term across all servers."

ltl electionSafety {
always (
forall (i:0..N - 1) forall (j:0..N - 1)
(i != j && currentTerm[i] == currentTerm[j] && state[i] == leader && state[j] == leader) -> false
)
}
```
