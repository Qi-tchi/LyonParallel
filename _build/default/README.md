## Installation

1. ```bash
   # Initialize OPAM (if not already initialized)
   opam init

   # Create and switch to a new OPAM switch
   opam switch create icgt25 5.2.1

   # Install packages
   opam install dune batteries domainslib atomic z3 core ppx_inline_test ppx_expect

   eval $(opam env)
   ```
2. **Build the Project** using Dune:The project is configured with a `dune` file that specifies the library and executable targets along with their dependencies.

   ```bash
   # Build the project
   dune build

   # Install
   dune install
   ```
3. **Run the Executable**:
   After a successful build, execute the REPL:

   ```bash
   # Using dune exec
   Icgt25
   ```

   Upon launching, you should see:

   ```
   Type 'help' for a list of commands.
   >>
   ```

---

### Try Type Graph Method with Non-well-founded Semirings

**Example Usage:**

```
systems
```

This command lists all **available** systems.

```
>> try_type_graph 0 30.0 a
```

This command will:

* Run the type graph method over the **arctic real semiring** (`a`)
* On the system at index `0`
* With a timeout of `30.0` seconds per method

**Available Semirings:**

- `a`: Arctic real semiring
- `n`: Arithmetic real semiring
- `t`: Tropical real semiring
- `A`: Arctic natural semiring
- `N`: Arithmetic natural semiring
- `T`: Tropical natural semiring

**General Syntax:**

```
>> try_type_graph [index] [timeout] [semiring_1 semiring_2 ...]
```

Example:

```
>> try_type_graph 3 30.0 a n t A N T
```

* Runs the type graph method over **all semirings in parallel**
* On the system at index `3`
* With a 30.0-second timeout per method

```
>> showme
```

Displays the constructed weighted type graphs.

* The type graph method is defined in
  `lib/parallel.ml` and `lib/termination.ml`

---

### Try Subgraph Counting Method

**Implementation Notes:**

- A restricted version of the termination method from Section 3 of the paper.
- Uses a stricter non-increasing rule definition:
  - The union of $h_{R'L}$ for all $R'\in D(R,X)$ must be an edge-injective graph homomorphism.
  - Node-injective required if $X$ has isolated nodes.
- Rule-set $\mathbb{X}$ is constrained to be a singleton.
- The tool systematically evaluates every subgraph of the left-hand-side graphs in the rewriting rules.

**Usage:**

```
systems
```

Lists all available systems.

```
>> try_subgraph_counting 41
```

Attempts to prove termination for the system at index `41`. On success:

```
!!! Termination proved !!!!
...
```

* The subgraph counting method is defined in
  `lib/termination.ml`

---

### Available Systems

* Systems are defined in:
  `lib/concreteGraphRewritingSystems.ml`

---

### Command Reference

- **`help`**Displays help message with usage instructions and commands.
- **`exit`**Exits the REPL.
- **`recap`**Prints session summary:
  - Selected system
  - Remaining rules
  - Applied strategies
  - Termination status
  - Elapsed runtime
