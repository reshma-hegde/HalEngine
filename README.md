# HalEngine — A High-Level Programming Language

HalEngine is a high-level programming language and compiler designed to explore low-level control, multi-threading, LLVM IR generation, and modern programming features.

## Features

- **Qubits and built-in quantum gates**
- **Rewind and Fastforward** — Temporally revert or advance variable states
- **Parallel Universe Model** — Execute alternate timelines of computation in isolation
- **Time-scope variables and history retrieval**
- **Reactive Variables** — Automatically update dependent computations
- **Automatic type inference**
- **Complex number and vector handling**
- **Sleep and timing constructs** (`sleep(500ms)` / `sleep(2s)`)
- **Function return type inference**
- **High-level print system** with support for arrays and vectors
- **Fine-grained control flow** (`if ... fi`, `else ... esle`, `while ... elihw`)
- **Support for arrays** (static and dynamic)

## Running HalEngine

You can run HalEngine on Windows using the provided executable:

1. Open a terminal (Command Prompt or PowerShell).
2. Navigate to the HalEngine directory containing `halengine.exe` and create a file with an extension .hal.
3. Run a HAL program using:
```bash
halengine.exe path\to\your\program.hal
```
## VS Code Extension

Enhance your HalEngine programming experience with syntax highlighting, code snippets, and debugging support using the official HalEngine VS Code Extension:  
[Download HalEngine VS Code Extension](https://marketplace.visualstudio.com/items?itemName=reshmahegde.halengine)  

*(Or install directly in VS Code by searching for “HalEngine” in the Extensions tab.)*



## Example Programs

### 1. Your first program
```hal
fun main()
   print("Hello World!");
   return 0;
nuf
```

### 1. Basic Computation
```hal
fun main()
    var a = 10;
    var b = 20;
    var c = a + b;
    print("Sum:", c);
    return 0;
nuf
```
### 2. Basic Quantum Gates
```hal
fun main()
    qubit q1;
    qubit q2;
    var r1 = measure q1;
    var r2 = measure q2;
    print("after (H)");
    print("q1: ", r1);
    print("q2: ", r2);

    H(q1);
    CNOT(q1,q2);
    
    r1 = measure q1;
    r2 = measure q2;
    print("after (CNOT)");
    print("q1: ", r1);
    print("q2: ", r2);
    return 0;
nuf
```
### 3. Reactive Variables
```hal
fun main()
    var x = 10;
    var y = reactive(x * 2);
    print("Initial y:", y); @ 20
    x = 15;
    print("Updated y:", y); @ 30
    return 0;
nuf
```
### 4. Time Scope Variables
```hal
fun load_data()
    return [1, 2, 3];
nuf
fun main()
    var cache = load_data() ~5s;
    print("cache data : ",cache);@[1,2,3]
    sleep(6s);
    print("cache data : ",cache);@null
    return 0;
nuf
```
### 5. Parallel universe execution
```hal
fun main()
    var x = 5;
    fork
        x = x + 1;
    or
        x = x * 2;
    merge result;
    print("forked result:",result);@[6,10]
    return 0;
nuf

```

## License

HalEngine is licensed under the GNU General Public License v3.0 (GPLv3).  
See [LICENSE](LICENSE.md) for the full license text.




