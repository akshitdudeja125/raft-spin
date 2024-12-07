In Promela, labels are static identifiers attached to specific points in your code. They cannot be dynamically created or parameterized based on variables like loop indices. This means that when you convert your code to use a loop for scalability, you cannot generate labels like `end_rv_1` dynamically inside the loop.

Here's your original code snippet for reference:

```promela
if
    :: (serverId != 0) ->
        end_rv_0: requestVoteChannels[serverId].ch[0]!requestVote
    :: (serverId != 1) ->
        end_rv_1: requestVoteChannels[serverId].ch[1]!requestVote
    :: (serverId != 2) ->
        end_rv_2: requestVoteChannels[serverId].ch[2]!requestVote
fi
```

Now, you have optimized your code to handle `n` servers using a loop, like this:

```promela
#define N 3 // Number of servers
int i;

for (i : 0 .. N-1) {
    if (serverId != i) {
        requestVoteChannels[serverId].ch[i]!requestVote;
    }
}
```

**Your Question:**

_How do I define labels like `end_rv_1` in the new code where I have `n` servers and can't hardcode these states?_

**Answer:**

Since labels in Promela cannot be dynamically generated or parameterized with variables, you can't create unique labels like `end_rv_i` inside a loop for each iteration `i`. However, there are alternative ways to achieve the same functionality you had with the labels in your original code.

Here are some approaches you can consider:

### **Option 1: Use Variables to Record Events**

Instead of using labels, you can declare an array of boolean variables (flags) to record when certain events happen for each server. This approach allows you to track specific actions associated with each server without needing separate labels.

**Example Implementation:**

1. **Declare an Array of Flags:**

   ```promela
   #define N 3 // Number of servers
   bool end_rv[N]; // Initialize all elements to false
   ```

2. **Modify Your Loop to Set the Flags:**

   ```promela
   int i;

   for (i : 0 .. N-1) {
       if (serverId != i) {
           requestVoteChannels[serverId].ch[i]!requestVote;
           end_rv[i] = true; // Record that requestVote was sent to server i
       }
   }
   ```

3. **Use the Flags in Your LTL Properties or Assertions:**

   You can now refer to `end_rv[i]` in your LTL properties or assertions to check whether `requestVote` was sent to server `i`.

   **Example LTL Property:**

   Suppose you want to assert that a `requestVote` is eventually sent to server `i` by `serverId`:

   ```
   [] (serverId != i -> <> end_rv[i])
   ```

   This property states that for all times, if `serverId` is not `i`, then eventually (`<>`) `end_rv[i]` becomes true, meaning a `requestVote` was sent to server `i`.

**Benefits of Using Variables:**

- **Scalable:** Works with any number of servers without hardcoding labels.
- **Specificity:** Allows you to track actions for each server individually.
- **Flexibility:** You can reset or update the flags as needed in your model.

### **Option 2: Use a Single Label and Context Information**

If you must use a label, you can place a single label inside the loop. However, since the label cannot change with each iteration, it won't distinguish between different servers. You might combine this with context variables to achieve your goal.

**Example:**

```promela
int i;

for (i : 0 .. N-1) {
    if (serverId != i) {
        end_rv: requestVoteChannels[serverId].ch[i]!requestVote;
        // You can use 'i' to know which server was involved
    }
}
```

In this case, `end_rv` is the same label for all iterations. While this doesn't give you unique labels per server, you can use the value of `i` (which server you're interacting with) in your verification properties.

**Limitation:**

- You cannot refer to `end_rv_i` for a specific server `i` in your LTL properties or assertions because the label is not unique per server.

### **Option 3: Expand the Loop Manually (Not Recommended for Large N)**

If `N` is small and manageable, you could unroll the loop manually and define labels for each case. However, this approach is not scalable and defeats the purpose of optimizing your code.

**Example:**

```promela
if
    :: (serverId != 0) ->
        end_rv_0: requestVoteChannels[serverId].ch[0]!requestVote
    :: (serverId != 1) ->
        end_rv_1: requestVoteChannels[serverId].ch[1]!requestVote
    :: (serverId != 2) ->
        end_rv_2: requestVoteChannels[serverId].ch[2]!requestVote
fi
```

**Limitation:**

- Not practical for large values of `N`.

### **Option 4: Use Macros to Generate Code with Labels**

In Promela, you can use the C preprocessor to define macros that generate code with labels. However, the macros themselves can't create dynamic labels based on variables at runtime.

**Example:**

```promela
#define SEND_REQUEST_VOTE(server) \
    if (serverId != server) { \
        end_rv_##server : requestVoteChannels[serverId].ch[server]!requestVote; \
    }

SEND_REQUEST_VOTE(0)
SEND_REQUEST_VOTE(1)
SEND_REQUEST_VOTE(2)
// ... up to N-1
```

**Note:** The `##` operator in macros concatenates tokens, allowing you to create unique labels like `end_rv_0`, `end_rv_1`, etc.

**Limitation:**

- Again, not practical for large `N` as it requires manually invoking the macro for each server.

### **Option 5: Adjust Your Verification Approach**

Since labels can't be parameterized, you might need to adjust how you specify your verification conditions. Instead of relying on labels, you can formulate your LTL properties based on the behavior or state changes that occur in your model.

**Example:**

If you need to verify that a `requestVote` message is sent to every other server, you can express this property in terms of the messages and variables in your model.

**LTL Property Without Labels:**

```
[] forall (i : int where 0 <= i && i < N && i != serverId) {
    ( requestVoteSentTo[i] == true )
}
```

Here, `requestVoteSentTo[i]` is a boolean array that you update in your code whenever a `requestVote` is sent to server `i`. This property asserts that, always (`[]`), for all `i` not equal to `serverId`, `requestVoteSentTo[i]` should eventually be `true`.

**Implementing `requestVoteSentTo` in Your Code:**

```promela
bool requestVoteSentTo[N]; // Initialize to false

int i;

for (i : 0 .. N-1) {
    if (serverId != i) {
        requestVoteChannels[serverId].ch[i]!requestVote;
        requestVoteSentTo[i] = true; // Record the sent message
    }
}
```

### **Summary and Recommendation:**

Given the limitations of labels in Promela, the most practical and scalable approach is to use variables (Option 1) to record the occurrences of events like sending `requestVote` messages. This way, you can track actions for each server individually without needing dynamic labels.

**Steps to Implement This Approach:**

1. **Declare an Array of Flags:**

   ```promela
   #define N 3 // Or any number of servers
   bool end_rv[N]; // Automatically initialized to false
   ```

2. **Update the Flags in Your Loop:**

   ```promela
   int i;

   for (i : 0 .. N-1) {
       if (serverId != i) {
           requestVoteChannels[serverId].ch[i]!requestVote;
           end_rv[i] = true; // Mark that requestVote was sent to server i
       }
   }
   ```

3. **Use the Flags in Verification:**

   - **In LTL Properties:**

     Express properties using `end_rv[i]` to refer to whether `requestVote` was sent to server `i`.

     **Example:**

     ```
     [] forall (i : int where 0 <= i && i < N && i != serverId) {
         ( end_rv[i] == true )
     }
     ```

   - **In Assertions:**

     Use `assert(end_rv[i] == true)` at appropriate points in your code to ensure that the `requestVote` message has been sent to each server `i`.

**Advantages of This Approach:**

- **Scalability:** Works for any number of servers without code duplication.
- **Clarity:** Keeps your code clean and maintainable.
- **Verification-Friendly:** Allows you to write precise verification properties.

**Additional Tips:**

- **Resetting Flags:** If you have multiple rounds or terms in your model, remember to reset the `end_rv` array when appropriate.
- **Synchronization:** Ensure that updates to shared variables like `end_rv` are done safely if you have concurrent processes that might access them.
- **Documentation:** Comment your code to explain the purpose of the `end_rv` array, especially for those who might read or maintain your model in the future.

### **Conclusion:**

While you cannot create dynamic labels in Promela to match each loop iteration, using variables like an array of booleans (`end_rv[]`) provides a robust and scalable solution. This method allows you to track and verify events associated with each server individually, achieving the same goals you had with the hardcoded labels in your original code.

By adopting this approach, you maintain the scalability and readability of your code while still being able to perform detailed verification for each server in your model.

---

**References:**

- **Promela Language Reference:** [Spin Verification Tool Documentation](http://spinroot.com/spin/Man/README.html)
- **Modeling Tips:** [Practical Spin Model Checking](http://spinroot.com/spin/Doc/book.html)

If you have further questions or need clarification on implementing this solution, feel free to ask!
