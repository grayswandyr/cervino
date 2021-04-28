#Protocol from the paper

All models for the protocols presented in the paper are in the CAV2021 folder.

##GSet
Model in gset.cervino. G-Set consists in a set a sets containing some elements, there is two possible events :
	-adding an element to a set
	-merging two sets by adding all element to a set to another set

##2PSet
Model in 2pset.cervino. G-Set consists in a set a sets containing some elements, there is three possible events :
	-adding an element to a set
	-removing an element to a set
	-merging two sets, the merged set corresponds to the set of elements added to one of the set that were not removed in any of the set


##FIFO
Model in fifo.cervino. It consists in a waiting list following the first-in first-out principle. There is two possible events :
	-some element is added to the bottom of the list
	-the head of the list exits it


##Leader election

Model in leader.cervino. The leader election protocol as presented in the paper consists in a ring-shaped network where each node possess a unique identifier, the protocol aims to elect the node with the greater identifier. Each node maintains a list of identifiers to send to its successor, a node is elected when it receives its own identifier. There is one possible operation : a node sends its own identifier and all identifiers in its list to its successor, then its successor adds all sent identifiers that are greater than its own identifier to its list.




##Lock Server
Model in lock.cervino. The lock server protocol features a single server and an unbounded number
of clients willing to hold a lock. There is 4 possible events :
	-a client can ask for the lock, then entering a waiting list
	-the server can grant the lock to a client
	-a client can send a message to the server to free the lock
	-the server can aknowledge than a client has freed the lock and take it back

##Dinning Philosophers
Model in philo.cervino. It features a set of philosophers in a ring-shaped maneer. Each philosopher has a right and left neighbor and a fork to its right and to its left. The protocol features three events:
	-a philosopher take a fork
	-a philosopher with both forks eat and put back forks on the table
	-a philosopher become hungry

##TLB-Shootdown
Model in TLB.cervino. The TLB Shootdown algorithm features a set of CPUs and a set of page tables, each CPU maintains a cache for a certain page table. The algorithm aims to keep this cache in sync when the page tables are updated. In our model we operated a simplification as we do not consider a set of page tables, we focus on CPUs and added a flag for CPUs indicating if some CPU has modified a page table or updated its cache.
In this algorithm any update is done through four phases.
The first phase is when a processor initiates an update phase then becoming an initiator, it set an "action needed" flag on other CPUs and send them a signal to interrupt them and waits for the response of others CPU. The second phase is when an other CPU receives the interrupt and then enters a responder phase. It then signals that it is not active by setting their active flag to false and waits. The initiator waits until all other CPUs have set their active flag to false, then it continues in phase 3. Phase 3 consists in the initiator updating the page table and its TLB, when the initiator has finished the responder then flush their own TLB and reset their "action needed" flag. Events correspond to executing an atomic operation of these phases. The safety property that is verified is that if a modification is done then any cpu do an update before coming back to its main loop.

##Token Ring
Model in mailbox_token.cervino. The protocol features a ring-shaped network where nodes are passing a token to each others. Passing the token is done in two steps:
	-sending the token, a node send a message to its successor in the ring to notify that it can take the token
	-receiving the token, a node that has been notified can take the token

#Models added for the artifact

##Leader election
leader_send_id.cervino is the cervino file for another version of the leader election protocol where only one id is sent by the send operation, verification on this version of the protocol results on a timeout.

##Ticket protocol
Model in ticket.cervino. The tiket protocol taken from [1] features a set a processes waiting to enters a critical section. The processes than can take a ticket and the process with the lowest ticket can enters the critical section. There is three possible events :
	-some process take a ticket
	-the process with the lowest ticket enters critical section
	-the process in critical section exit it
The liveness property is that any process taking a ticket eventually enters critical section. For this models the verification procedure using TEA fails.

##Notification protocol
Model in notification.cervino, the notification protocol is a toy protocol taken from [2]. It features a ring-shaped network where nodes can be notified or unnotified. There is only one operation that consists in a node notifying its successor.


