import sys
import os
import platform 
import subprocess
from llvmlite import ir
import llvmlite.binding as llvm
from ctypes import CFUNCTYPE, c_int, c_float
from lexer import Lexer
from AST import Program
from Parser import Parser
from Compiler import Compiler
import json
import time

#python main.py tests/thread.hal
#llc -filetype=obj debug/ir.ll -o output.o
#gcc output.o -o thread.exe -lpthread
#./thread

LEXER_DEBUG: bool = False
PARSER_DEBUG: bool = True
COMPILER_DEBUG: bool = True
RUN_CODE: bool = True

if __name__ == '__main__':
    try:
        if len(sys.argv) < 2:
            print("Usage: python main.py <file.hal>")
            exit(1)

        hal_file = sys.argv[1]

        with open(hal_file, "r") as f:
            code: str = f.read()
      
        if LEXER_DEBUG:
            print("LEXER DEBUGGING")
            debug_lex: Lexer = Lexer(source=code)
            while debug_lex.current_char is not None:
                print(debug_lex.next_token())

        l: Lexer = Lexer(source=code)
        
        p: Parser = Parser(lexer=l)

        program: Program = p.parse_program()
        if len(p.errors) > 0:
            for err in p.errors:
                print(err)
            exit(1)

        if PARSER_DEBUG:
            print("==== PARSER DEBUG ====")
            
            os.makedirs("debug", exist_ok=True)
            with open("debug/ast.json", "w") as f:
                json.dump(program.json(), f, indent=4)
            print("Successful!")
        
        c: Compiler = Compiler()
        c.compile(node=program)
        
        llvm_module: ir.Module = c.module

        
        llvm_module.triple = llvm.get_default_triple()

        if COMPILER_DEBUG:
            os.makedirs("debug", exist_ok=True)
            with open("debug/ir.ll", "w") as f:
                f.write(str(llvm_module))
        
        if RUN_CODE:
            llvm.initialize()
            llvm.initialize_native_target()
            llvm.initialize_native_asmprinter()

            system = platform.system()
            if system == "Linux":
                
                try:
                    llvm.load_library_permanently('libpthread.so.0')
                except RuntimeError:
                    print("Warning: Could not load 'libpthread.so.0'. A newer version might be used by default.")
            elif system == "Darwin": 
                llvm.load_library_permanently('libpthread.dylib')
            
            try:
                llvm_ir_parsed = llvm.parse_assembly(str(llvm_module))
                llvm_ir_parsed.verify()
            except Exception as e:
                print("LLVM verification error")
                raise 

            target_machine = llvm.Target.from_default_triple().create_target_machine()
            engine = llvm.create_mcjit_compiler(llvm_ir_parsed, target_machine)
            engine.finalize_object()
            
            entry = engine.get_function_address('main')
            if entry == 0:
                raise RuntimeError("Function 'main' not found in LLVM module.")
            
            func_info = c.env.lookup("main")
            if func_info is None:
                raise RuntimeError("Could not find 'main' in compiler environment.")

            _, ret_type = func_info 
            if isinstance(ret_type, ir.IntType):
                CFUNC = CFUNCTYPE(c_int)
            elif isinstance(ret_type, ir.FloatType):
                CFUNC = CFUNCTYPE(c_float)
            else:
                print(f"Warning: Unsupported return type for main(): {ret_type}. Defaulting to int.")
                CFUNC = CFUNCTYPE(c_int)

            cfunc = CFUNC(entry)
            st = time.time()
            result = cfunc()
            et = time.time()
            print(f'\n====Program returned {result} executed in {round((et-st)*1000,6)}ms====')
            
    except SyntaxError as e:
        print(f"SyntaxError: {e}") 
    except Exception as e:
        print(f"Error: {e}")