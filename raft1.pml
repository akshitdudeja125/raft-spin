

#define N 3// Defining max possible servers
#define MAX_TERM 3// Defining max possible terms
#define MAX_LOG 2// Defining max possible logs
#define NONE 111

// Message Channels
typedef AppendEntry {
	byte term;// The LEADER's current term.
	byte senderId;// LEADER Id
	byte index;// Index of the log entry being proposed
	byte prevLogTerm;// Term of prevLogIndex entry
	byte LEADERCommit;// LEADER's commitIndex
}

// chan appendEntryChannels[N] = [N] of {AppendEntry};

typedef AppendEntryChannels {
chan ch[N] = [1] of { AppendEntry };
};
//this line means that there are N channels of type AppendEntry, and each channel has a buffer size of 1. The array is indexed by the serverId, so each server has its own channel to send AppendEntry messages to other servers.
//Why is the buffer size 1?
//The buffer size is 1 because we only need to store the latest AppendEntry message in the channel. If a new message is sent before the previous one is read, the previous message will be overwritten. This is sufficient for the Raft consensus algorithm, where only the latest message is relevant.
AppendEntryChannels appendEntryChannels[N];

// Response to AppendEntry
typedef AppendEntryResponse {
	byte term;
	byte senderId;
	bool success;
	
};

typedef AppendEntryResponseChannels {
chan ch[N] = [1] of { AppendEntryResponse };
};
AppendEntryResponseChannels appendEntryResponseChannels[N];


typedef RequestVote {
	byte term;// Candidate's term
	byte senderId;// Candidate requesting vote
	byte lastLogIndex;// Index of candidate's last log entry
	byte lastLogTerm;// Term of candidate's last log entry
}

// chan requestVoteChannels[N] = [N] of {RequestVote};
typedef RequestVoteChannels {
chan ch[N] = [1] of { RequestVote };
};
RequestVoteChannels requestVoteChannels[N];
//Explain this line with syntax
//chan requestVoteChannels[N] = [N] of {RequestVote};	
// This line creates an array of channels, each channel is of type RequestVote and there are N channels in total. The array is indexed by the serverId, so each server has its own channel to send RequestVote messages to other servers.

typedef RequestVoteResponse {
	byte term;// Current term for candidate to update itself
	bool voteGranted;// True means candidate received vote
	byte senderId;// Sender Id
}
typedef RequestVoteResponseChannels {
chan ch[N] = [1] of { RequestVoteResponse };
};

RequestVoteResponseChannels requestVoteResponseChannels[N];

// Global Variables
mtype:State = { LEADER,FOLLOWER,CANDIDATE };// Enum for State
mtype:State state[N];




byte currentTerm[N] = 0;// Latest term server has seen

typedef Logs{
	byte log[2];
}
Logs logs[N];// Log entries;each entry contains command for state machine,and term when entry was received by LEADER (first index is 1)
byte commitIndex[N] = 0;// Index of highest log entry known to be committed

// Helper Functions

// Function to get the majority
inline majority() {
	((N / 2) + 1)
}


proctype server(byte serverId){ 
	state[serverId] = FOLLOWER;
	byte i;
	byte votesGranted[N] = false;
	byte votedFor = NONE;
	RequestVote requestVote;
	byte lastLogTerm,lastLogIndex;
	RequestVoteResponse requestVoteResponse;
	bool logOk;
	
	AppendEntry appendEntry;
	AppendEntryResponse appendEntryResponse;
	int voteCount = 0;
	
	do
	:: // timeout
		(state[serverId] == FOLLOWER || state[serverId] == CANDIDATE) -> 
		atomic{
			state[serverId] = CANDIDATE;
			currentTerm[serverId] = currentTerm[serverId] + 1;
			
			end_max_term: if
			:: (currentTerm[serverId] <= MAX_TERM) -> skip
// :: else -> break
			fi
			votedFor = serverId;
			i = 0;
			do
			:: (i < N) -> 
				votesGranted[i] = 0;
				i++
			:: else -> break
			od
			votesGranted[serverId] = 1;
		}
	:: // restart
// When is this called?
// When the server is a candidate and receives a message from another server with a term greater than the current term of the server. The server will update its term to the term received in the message and change its state to FOLLOWER. The server will also update its votedFor variable to NONE.
		state[serverId] = FOLLOWER;
		
	:: (state[serverId] == CANDIDATE) -> 
		atomic{
			requestVote.term = currentTerm[serverId];
			i = 0;			
			do
			:: (i < MAX_LOG) -> 
				if
				:: (logs[serverId].log[i] == 0) -> 
					if
					:: (i == 0) -> requestVote.lastLogTerm = 0;
					:: else -> requestVote.lastLogTerm = logs[serverId].log[i - 1];
					fi;
					requestVote.lastLogIndex = i;
					break;// Exit the loop once the last log entry is determined
				:: (i == MAX_LOG - 1) -> 
// Set to the last entry if all previous entries are non-zero
					requestVote.lastLogTerm = logs[serverId].log[i];
					requestVote.lastLogIndex = i + 1;
					break;
				fi;
				i = i + 1;
			:: (i >= MAX_LOG) -> break;
			od;
			
			if
			:: (serverId != 0) -> 
				end_rv_0:           requestVoteChannels[serverId].ch[0]!requestVote
			:: (serverId != 1) -> 
				end_rv_1:           requestVoteChannels[serverId].ch[1]!requestVote
			:: (serverId != 2) -> 
				end_rv_2:           requestVoteChannels[serverId].ch[2]!requestVote
			fi
// for (i : 0 .. N - 1) {// Loop over all server IDs
// 	if
// 	:: (serverId != i) -> // Exclude the current serverId
// 		end_rv requestVoteChannels[serverId].ch[i]!requestVote
// 	:: else -> skip// Do nothing if serverId == i
// 	fi
// }
// In the above 5 lines of code, the server sends a RequestVote message to all other servers except itself.
// Why is it sending a RequestVote message to all and not sending to a random server?
// The server sends a RequestVote message to all other servers because it needs to get votes from a majority of the servers to become the LEADER. If it only sent the message to a random server, it might not get enough votes to become the LEADER.
		}
	:: // become LEADER
		(state[serverId] == CANDIDATE) -> 
		voteCount = 0;
		i = 0;
		do
		:: (i < N) -> 
			voteCount = voteCount + votesGranted[i];
			i = i + 1;
		:: (i >= N) -> break;
		od;
		if
		:: (voteCount >= N / 2 + 1) -> 
			state[serverId] = LEADER;
		:: else -> skip
		fi
		
// Handle RequestVote
		
	:: atomic {
			i = 0;
			do
			:: (i < N) -> 
				if
				:: (len(requestVoteChannels[i].ch[serverId]) > 0) -> assert(i != serverId);
					requestVoteChannels[i].ch[serverId]?requestVote;
// Valid channel with valid Vote found
					if
					:: (requestVote.term > currentTerm[serverId]) -> 
						currentTerm[serverId] = requestVote.term;
						state[serverId] = FOLLOWER;
						votedFor = NONE;
					:: (requestVote.term <= currentTerm[serverId]) -> skip
					fi
					
					i = 0;
					do
					:: (i < MAX_LOG) -> 
						if
						:: (logs[serverId].log[i] == 0) -> 
							if
							:: (i == 0) -> lastLogTerm = 0;
							:: else -> lastLogTerm = logs[serverId].log[i - 1];
							fi;
							lastLogIndex = i;break;
						:: (i == MAX_LOG - 1) -> 
							lastLogTerm = logs[serverId].log[i];
							lastLogIndex = i + 1;break;
						fi;
						i = i + 1;
					:: (i >= MAX_LOG) -> break;
					od;
					
					logOk = requestVote.lastLogTerm > lastLogTerm || requestVote.lastLogTerm == lastLogTerm && requestVote.lastLogIndex >= lastLogIndex;
					requestVoteResponse.voteGranted = (requestVote.term == currentTerm[serverId]) && logOk && (votedFor == NONE || votedFor == i);
					
					requestVoteResponse.term = currentTerm[serverId];
					if
					:: requestVoteResponse.voteGranted -> votedFor = i
					:: !requestVoteResponse.voteGranted -> skip
					fi
					end_requestVoteResponse:        requestVoteResponseChannels[i].ch[serverId]!requestVoteResponse
					break;
				:: else -> i = i + 1
				fi
			:: else -> 
				break;
			od;
			break
		}
		
// :: // Handle RequestVoteResponse
// 	(
// 	requestVoteResponseChannels[0].ch[serverId]?[requestVoteResponse] || 
// 	requestVoteResponseChannels[1].ch[serverId]?[requestVoteResponse] || 
// 	requestVoteResponseChannels[2].ch[serverId]?[requestVoteResponse]
// 	) -> 
// 	atomic{
			
// 		i = 0;
// 		do 
// 		:: (i < N) -> 
// 			if
// 			:: requestVoteResponseChannels[i].ch[serverId]?requestVoteResponse -> break;
// 			fi;
// 			i = i + 1;
// 		:: (i >= N) -> break;
// 		od;
// 		assert(i != serverId);// Ensure a valid channel was found and it's not self
			
// 		if
// 		:: (requestVoteResponse.term > currentTerm[serverId]) -> 
// 			currentTerm[serverId] = requestVoteResponse.term;
// 			state[serverId] = FOLLOWER;
// 			votedFor = NONE;
// 		:: (requestVoteResponse.term == currentTerm[serverId] && requestVoteResponse.voteGranted) -> 
// 			votesGranted[i] = 1;
// 		:: !(requestVoteResponse.term > currentTerm[serverId]) && !(requestVoteResponse.term == currentTerm[serverId] && requestVoteResponse.voteGranted) -> 
// 		fi
// 	}
		
		
	:: // handle RequestVoteResponse
		atomic {
			i = 0;
			do
			:: (i < N) -> 
				if
				:: (len(requestVoteResponseChannels[i].ch[serverId]) > 0) -> 
					assert(i != serverId);
					requestVoteResponseChannels[i].ch[serverId]?requestVoteResponse;
					
// Valid channel with valid Vote found
					if
					:: (requestVoteResponse.term > currentTerm[serverId]) -> // update terms
						currentTerm[serverId] = requestVoteResponse.term;
						state[serverId] = FOLLOWER;
						votedFor = NONE
					:: (requestVoteResponse.term == currentTerm[serverId] && requestVoteResponse.voteGranted) -> 
						votesGranted[i] = 1
					:: !(requestVoteResponse.term > currentTerm[serverId]) && !(requestVoteResponse.term == currentTerm[serverId] && requestVoteResponse.voteGranted) -> 
						skip
					fi
				:: else -> 
					i = i + 1
				fi
			:: else -> 
				break;
			od;
			break
		}
		
		
	:: // Append Entries
		(state[serverId] == LEADER) -> 
		atomic{
			appendEntry.term = currentTerm[serverId];
			appendEntry.senderId = serverId;
			appendEntry.index = 0;
			
			do
			:: (i < N) -> 
				if
				:: (i != serverId) -> 
					atomic{
						int j = 0;
						do
						:: (j < MAX_LOG) -> 
							if
							:: (logs[serverId].log[j] != logs[i].log[j]) -> 
								appendEntry.index = j;
								appendEntry.prevLogTerm = logs[i].log[j - 1];
								break;
							fi;
							j = j + 1;
						:: (j >= MAX_LOG) -> break;
						od;
						
					}
					end_appendEntry:        appendEntryChannels[serverId].ch[i]!appendEntry
				fi;
				i++;
			:: else -> break
			od
		}
		
		
		
// 	:: // handle AppendEntry
		
// 		(appendEntryChannels[0].ch[serverId]?[appendEntry] || appendEntryChannels[1].ch[serverId]?[appendEntry] || appendEntryChannels[2].ch[serverId]?[appendEntry]) -> 
// 		atomic {
// 			i = 0;
// 			do 
// 			:: (i < N) -> 
// 				if
// 				:: appendEntryChannels[i].ch[serverId]?appendEntry -> break;
// 				fi;
// 				i = i + 1;
// 			:: (i >= N) -> break;
// 			od;
// 			assert(i != serverId);// Ensure a valid channel was found and it's not self
// // Update terms
// 			if
// 			:: (appendEntry.term > currentTerm[serverId]) -> 
// 				currentTerm[serverId] = appendEntry.term;
// 				state[serverId] = FOLLOWER;
// 				votedFor = NONE;
// 			:: (appendEntry.term <= currentTerm[serverId]) -> 
// 				skip
// 			fi
// 			assert(appendEntry.term <= currentTerm[serverId]);	
			
// // Return to FOLLOWER state
// 			if
// 			:: (appendEntry.term == currentTerm[serverId] && state[serverId] == CANDIDATE) -> 
// 				state[serverId] = FOLLOWER;
// 				votedFor = NONE;
// 			:: (appendEntry.term != currentTerm[serverId] || state[serverId] != CANDIDATE) -> 
// 				skip;
// 			fi
// 			assert(!(appendEntry.term == currentTerm[serverId]) || (state[serverId] == FOLLOWER));
// 			logOk = appendEntry.index == 0 || (appendEntry.index == 1 && appendEntry.prevLogTerm == logs[serverId].log[0]);
// 			if
// 			:: (appendEntry.term < currentTerm[i] || appendEntry.term == currentTerm[serverId] && state[serverId] == FOLLOWER && !logOk) -> // reject request
// 				appendEntryResponse.success = 0;
// 				end_aer_rej:        appendEntryResponseChannels[serverId].ch[i]!appendEntryResponse
// 			:: (appendEntry.term == currentTerm[serverId] && state[serverId] == FOLLOWER && logOk) -> 
// 				appendEntryResponse.success = 1;
			
// 				logs[serverId].log[appendEntry.index] = appendEntry.term;
			
// 				commitIndex[serverId] = appendEntry.LEADERCommit;
			
// 				end_aer_acc:        appendEntryResponseChannels[serverId].ch[i]!appendEntryResponse
// 				fi	
// 			}
		
	:: // handle AppendEntry
		atomic{
			i = 0;
			do
			:: (i < N) -> 
				if
				:: (len(appendEntryChannels[i].ch[serverId]) > 0) -> 
					assert(i != serverId);
					appendEntryChannels[i].ch[serverId]?appendEntry;
// update terms
					if
					:: (appendEntry.term > currentTerm[serverId]) -> 
						currentTerm[serverId] = appendEntry.term;
						state[serverId] = FOLLOWER;
						votedFor = NONE;
					:: (appendEntry.term <= currentTerm[serverId]) -> 
						skip
					fi
					assert(appendEntry.term <= currentTerm[serverId]);
// Return to FOLLOWER state
					if
					:: (appendEntry.term == currentTerm[serverId] && state[serverId] == CANDIDATE) -> 
						state[serverId] = FOLLOWER;
						votedFor = NONE;
					:: (appendEntry.term != currentTerm[serverId] || state[serverId] != CANDIDATE) -> 
						skip
					fi
					assert(!(appendEntry.term == currentTerm[serverId]) || (state[serverId] == FOLLOWER));
					logOk = appendEntry.index == 0 || (appendEntry.index == 1 && appendEntry.prevLogTerm == logs[serverId].log[0]);
					if
					:: (appendEntry.term < currentTerm[i] || appendEntry.term == currentTerm[serverId] && state[serverId] == FOLLOWER && !logOk) -> // reject request
						appendEntryResponse.success = 0;
						end_aer_rej:        appendEntryResponseChannels[serverId].ch[i]!appendEntryResponse
					:: (appendEntry.term == currentTerm[serverId] && state[serverId] == FOLLOWER && logOk) -> 
						appendEntryResponse.success = 1;
						logs[serverId].log[appendEntry.index] = appendEntry.term;
						commitIndex[serverId] = appendEntry.LEADERCommit;
						end_aer_acc:        appendEntryResponseChannels[serverId].ch[i]!appendEntryResponse
					fi
				:: else -> 
					i = i + 1
				fi
			:: else -> 
				break;
			od;
			break;
			
		}
	:: // Handle AppendEntryResponse
		atomic{
			i = 0;
			do
			:: (i < N) -> 
				if
				:: (len(appendEntryResponseChannels[i].ch[serverId]) > 0) -> 
					assert(i != serverId);
					appendEntryResponseChannels[i].ch[serverId]?appendEntryResponse;
					if
					:: (appendEntryResponse.term > currentTerm[serverId]) -> // update terms
						currentTerm[serverId] = appendEntryResponse.term;
						state[serverId] = FOLLOWER;
						votedFor = NONE
					:: (appendEntryResponse.term < currentTerm[serverId]) -> 
						skip
					:: (appendEntryResponse.term == currentTerm[serverId] && appendEntryResponse.success && state[serverId] == LEADER) -> 
						if
						:: (commitIndex[serverId] == 0 && logs[i].log[0] == logs[serverId].log[0]) -> 
							commitIndex[serverId] = 1
						:: (commitIndex[serverId] == 1 && !(logs[serverId].log[1] != 0 && logs[i].log[1] == logs[serverId].log[1])) -> 
							skip
						fi
					:: (appendEntryResponse.term == currentTerm[serverId] && !(appendEntryResponse.success && state[serverId] == LEADER)) -> 
						skip
					fi
				:: else -> 
					i = i + 1
				fi
			:: else -> 
				break
			od;
			break
			
		}
		
	:: // handle Client Request
		(state[serverId] == LEADER && logs[serverId].log[MAX_LOG - 1] == 0) -> 
		logs[serverId].log[MAX_LOG - 1] = currentTerm[serverId]
	od;
// How is this working?
// WHen the state of the server is LEADER and the last log entry is empty, the server will add the current term to the last log entry. This is a simple way to handle client requests. The server will append the current term to the log entry and then the LEADER will send the AppendEntry message to all followers. The followers will then update their logs with the new term. This is a simple way to handle client requests in a distributed system.
	
// Why  is the last log entry empty?
// The last log entry is empty because the server has not received any client requests yet. The server will append the current term to the last log entry when it receives a client request. This is a simple way to handle client requests in a distributed system.
	
// What is the current term?
// The current term is the term that the server is currently in. The server will append the current term to the last log entry when it receives a client request. This is a simple way to handle client requests in a distributed system.
};

init {
	byte i;
	i = 0;
	do
	:: (i < N) -> 
		run server(i);
// print 
		printf("Server %d is running\n",i);
		i++
	:: else -> break
	od
}
ltl electionSafety {
	always!(
	(state[0] == LEADER && state[1] == LEADER && currentTerm[0] == currentTerm[1])
	|| (state[0] == LEADER && state[2] == LEADER && currentTerm[0] == currentTerm[2])
	|| (state[1] == LEADER && state[2] == LEADER && currentTerm[1] == currentTerm[2])
	)
}


// ltl electionLiveness {
// 	<> (state[0] == LEADER || state[1] == LEADER || state[2] == LEADER)
// }

// Difference b/w electionSafety and electionLiveness
// electionSafety is a safety property that ensures that if two servers are LEADERs, they have the same term. This property is always true in a correct Raft implementation.
// electionLiveness is a liveness property that ensures that eventually, one of the servers becomes the LEADER. This property is also always true in a correct Raft implementation.


// byte leaders = 0;

// lt electionSafety{
// 	always (leaders <= 1)
// }