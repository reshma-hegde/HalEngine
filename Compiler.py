import cmath
import math
import random
from llvmlite import ir
import os
from AST import DoubleLiteral, Node,NodeType,Program,Statement,Expression, VarStatement,IdentifierLiteral,ReturnStatement,AssignStatement,CallExpression,InputExpression,NullLiteral, ClassStatement,ThisExpression,BranchStatement,ForkStatement,QubitDeclarationStatement,MeasureExpression
from AST import ExpressionStatement,InfixExpression,IntegerLiteral,FloatLiteral, BlockStatement,FunctionStatement,IfStatement,BooleanLiteral,ArrayLiteral,RefExpression,DerefExpression,ReserveCall,RewindStatement, FastForwardStatement
from AST import FunctionParameter,StringLiteral,WhileStatement,BreakStatement,ContinueStatement,PrefixExpression,PostfixExpression,LoadStatement,ArrayAccessExpression, StructInstanceExpression,StructAccessExpression,StructStatement,QubitResetStatement
from typing import List, cast
from Environment import Environment
from typing import Optional
from lexer import Lexer
from Parser import Parser

BUILTIN_HEADERS = {
    
}


class Compiler:
    def __init__(self)-> None:
        self.errors: list[str] = []
        self.array_lengths: dict[str, int] = {}
        self.struct_types: dict[str, ir.IdentifiedStructType] = {}
        self.struct_layouts: dict[str, dict[str, int]] = {}
        self.class_methods: dict[str, list[str]] = {}
        self.type_map:dict[str,ir.Type]={
            'int':ir.IntType(32),
            'float':ir.FloatType(),
            'double':ir.DoubleType(),
            'void':ir.VoidType(),
            'bool':ir.IntType(1),
            'str':ir.PointerType(ir.IntType(8)),
            'null': ir.VoidType(),
            'qubit':ir.IntType(32)
        }
        
        self.counter:int=0
        self.module:ir.Module=ir.Module('main')
        self.true_str = ir.GlobalVariable(self.module, ir.ArrayType(ir.IntType(8), 5), name="true_str")
        self.true_str.global_constant = True
        self.true_str.linkage = 'internal'
        self.true_str.initializer = ir.Constant(ir.ArrayType(ir.IntType(8), 5), bytearray(b"true\0")) # type: ignore

        self.false_str = ir.GlobalVariable(self.module, ir.ArrayType(ir.IntType(8), 6), name="false_str")
        self.false_str.global_constant = True
        self.false_str.linkage = 'internal'
        self.false_str.initializer = ir.Constant(ir.ArrayType(ir.IntType(8), 6), bytearray(b"false\0")) # type: ignore
        self.builder:ir.IRBuilder=ir.IRBuilder()
        self.env:Environment=Environment()

        self.qubits: dict[str, dict] = {}
        self.qubit_states: dict[str, int] = {}  
        self.superposition_qubits: set[str] = set()
        self.entangled_pairs: dict[str, str] = {}

        self.__initialize_builtins()
        self.breakpoints:list[ir.Block]=[]
        self.continues:list[ir.Block]=[]
        self.global_parsed_pallets:dict[str,Program]={}

        self.history_vars: dict[str, tuple[ir.Value, ir.Type]] = {}
        self.history_idx_ptr: ir.Value | None = None
        self.history_len_ptr: ir.Value | None = None
        self.is_in_main: bool = False
        self.HISTORY_CAPACITY: int = 1024
        
        

    def __initialize_builtins(self)->None:
        
        def __init_print()->ir.Function:
            fnty:ir.FunctionType=ir.FunctionType(
                self.type_map['int'],
                [ir.IntType(8).as_pointer()],
                var_arg=True
            )
            return ir.Function(self.module,fnty,'printf')
        
        def __init_scanf()->ir.Function:
            fnty:ir.FunctionType=ir.FunctionType(
                self.type_map['int'],
                [ir.IntType(8).as_pointer()],
                var_arg=True
            )
            return ir.Function(self.module,fnty,'scanf')

        def __init_booleans()->tuple[ir.GlobalVariable,ir.GlobalVariable]:
            bool_type:ir.Type=self.type_map['bool']
            true_var=ir.GlobalVariable(self.module,bool_type,'true')
            true_var.initializer=ir.Constant(bool_type,1) # type: ignore
            true_var.global_constant=True
            false_var=ir.GlobalVariable(self.module,bool_type,'false')
            false_var.initializer=ir.Constant(bool_type,0) # type: ignore
            false_var.global_constant=True

            return true_var,false_var
        
        def __init_null()->ir.GlobalVariable:
            null_type = self.type_map['int'].as_pointer() # Using a null pointer for 'null'
            null_var = ir.GlobalVariable(self.module, null_type, 'null')
            null_var.initializer = ir.Constant(null_type, None) # type: ignore
            null_var.global_constant = True
            return null_var
        
              

        def __init_malloc()->ir.Function:
            fnty:ir.FunctionType=ir.FunctionType(
                ir.IntType(8).as_pointer(),
                [ir.IntType(32)],
                var_arg=False
            )
            return ir.Function(self.module,fnty,'malloc')
        
        def __init_free()->ir.Function:
            fnty:ir.FunctionType=ir.FunctionType(
                ir.VoidType(), 
                [ir.IntType(8).as_pointer()], 
                var_arg=False
            )
            return ir.Function(self.module, fnty, 'free')
        
        def __builtin_len(params: list[ir.Value], return_type: ir.Type):
            if len(params) != 1:
                self.report_error("len() requires exactly 1 parameter.")
                return None

            array_val = params[0]
            if array_val is None: 
                self.errors.append("ddd")
                return 
            array_type = getattr(array_val, "type", None)


            if isinstance(array_type, ir.ArrayType):
                return ir.Constant(ir.IntType(32), array_type.count)

            if isinstance(array_type, ir.PointerType) and isinstance(array_type.pointee, ir.ArrayType):  # type: ignore
                return ir.Constant(ir.IntType(32), array_type.pointee.count)  # type: ignore

            self.report_error("len() only works on fixed-size arrays right now.")
            return None
            
        
        def __init_time()->ir.Function:
            
            fnty = ir.FunctionType(ir.IntType(32), [ir.IntType(32).as_pointer()])
            return ir.Function(self.module, fnty, 'time')
        
        def __init_srand()->ir.Function:
           
            fnty = ir.FunctionType(ir.VoidType(), [ir.IntType(32)])
            return ir.Function(self.module, fnty, 'srand')

        def __init_rand()->ir.Function:
            
            fnty = ir.FunctionType(ir.IntType(32), [])
            return ir.Function(self.module, fnty, 'rand')

        
        self.env.define('time', __init_time(), ir.IntType(32))
        self.env.define('srand', __init_srand(), ir.VoidType())
        self.env.define('rand', __init_rand(), ir.IntType(32))

        self.builtin_functions = {}
        self.builtin_functions["len"] = __builtin_len


        
        #print
        self.env.define('print',__init_print(),ir.IntType(32))
        self.env.define('input',__init_scanf(),ir.IntType(32))
        self.env.define('reserve', __init_malloc(), ir.IntType(8).as_pointer())
        self.env.define('free', __init_free(), ir.VoidType())
        true_var,false_var=__init_booleans()
        self.env.define('true',true_var,true_var.type)
        self.env.define('false',false_var,false_var.type)

        null_var = __init_null()
        self.env.define('null', null_var, null_var.type)
        self.__initialize_math_builtins()

    def __initialize_math_builtins(self) -> None:
        """
        Initializes math functions (sin, cos, tan) with double precision.
        """
        double_type = ir.DoubleType()

        # Function signature: double name(double)
        fnty = ir.FunctionType(double_type, [double_type])

        # sin
        sin_func = ir.Function(self.module, fnty, 'sin')
        self.env.define('sin', sin_func, double_type)

        # cos
        cos_func = ir.Function(self.module, fnty, 'cos')
        self.env.define('cos', cos_func, double_type)

        # tan
        tan_func = ir.Function(self.module, fnty, 'tan')
        self.env.define('tan', tan_func, double_type)

       
    def increment_counter(self)->int:
        self.counter+=1
        return self.counter


    def compile(self, node: Node) -> None:
        match node.type():
            case NodeType.Program:
                self.visit_program(cast(Program, node))

            case NodeType.ExpressionStatement:
                self.visit_expression_statement(cast(ExpressionStatement,node))
            case NodeType.RewindStatement:
                self.visit_rewind_statement(cast(RewindStatement, node))
            case NodeType.QubitDeclarationStatement: 
                self.visit_qubit_declaration(cast(QubitDeclarationStatement, node))
            case NodeType.FastForwardStatement:
                self.visit_fastforward_statement(cast(FastForwardStatement, node))
            case NodeType.QubitResetStatement: 
                self.visit_qubit_reset(cast(QubitResetStatement, node))
            case NodeType.VarStatement:
                self.visit_var_statement(cast(VarStatement,node))
            case NodeType.ForkStatement:
                self.visit_fork_statement(cast(ForkStatement, node))
            case NodeType.InfixExpression:
                self.visit_infix_expression(cast(InfixExpression, node))
            case NodeType.PostfixExpression:
                self.visit_postfix_expression(cast(PostfixExpression, node))
            case NodeType.FunctionStatement:
                self.visit_function_statement(cast(FunctionStatement,node))
            case NodeType.BlockStatement:
                self.visit_block_statement(cast(BlockStatement,node))
            case NodeType.ReturnStatement:
                self.visit_return_statement(cast(ReturnStatement,node))
            case NodeType.AssignStatement:
                self.visit_assign_statement(cast(AssignStatement,node))
            case NodeType.IfStatement:
                self.visit_if_statement(cast(IfStatement,node))
            case NodeType.WhileStatement:
                self.visit_while_statement(cast(WhileStatement,node))
            case NodeType.ClassStatement:
                self.visit_class_statement(cast(ClassStatement,node))
            
            case NodeType.StructStatement:
                self.visit_struct_definition_statement(cast(StructStatement, node))
            
            case NodeType.CallExpression:
                self.visit_call_expression(cast(CallExpression,node))
            case NodeType.BreakStatement:
                self.visit_break_statement(cast(BreakStatement,node))
            case NodeType.ConinueStatement:
                self.visit_continue_statement(cast(ContinueStatement,node))
            case NodeType.LoadStatement:
                self.visit_load_statement(cast(LoadStatement,node))
            case NodeType.NullLiteral: 
                self.visit_null_literal(cast(NullLiteral, node))

  

    
    def visit_fork_statement(self, node: ForkStatement) -> None:
        if not node.branches:
            return 
         
        target_var_name: Optional[str] = None
        first_stmt = node.branches[0].statements[0]
        if isinstance(first_stmt, AssignStatement) and isinstance(first_stmt.ident, IdentifierLiteral):
            target_var_name = first_stmt.ident.value
        
        if target_var_name is None:
            self.report_error("Could not determine which variable is being modified in the fork block. The first statement in a branch must be an assignment.")
            return

        
        var_entry = self.env.lookup(target_var_name)
        if var_entry is None:
            self.report_error(f"Variable '{target_var_name}' used in fork block is not defined.")
            return
        var_ptr, var_type = var_entry

        initial_value = self.builder.load(var_ptr, name=f"{target_var_name}_snapshot")

        outcome_values: List[ir.Value] = []

        for branch in node.branches:
            
            self.builder.store(initial_value, var_ptr)
           
            self.compile(branch)
            
            final_value = self.builder.load(var_ptr, name=f"{target_var_name}_outcome")
            outcome_values.append(final_value)

        
        if not outcome_values:
            return

        merge_var_name = node.merge_variable.value
        if merge_var_name is None:
            self.report_error("Merge statement is missing a result variable name.")
            return

        num_outcomes = len(outcome_values)
       
        outcome_element_type = getattr(outcome_values[0], "type", None)
        array_type = ir.ArrayType(outcome_element_type, num_outcomes)

        result_array_ptr = self.builder.alloca(array_type, name=merge_var_name)

        for i, value in enumerate(outcome_values):
            idx = ir.Constant(ir.IntType(32), i)
            element_ptr = self.builder.gep(result_array_ptr, [ir.Constant(ir.IntType(32), 0), idx], inbounds=True)
            self.builder.store(value, element_ptr)

        self.env.define(merge_var_name, result_array_ptr, result_array_ptr.type)
        if merge_var_name:
             self.array_lengths[merge_var_name] = num_outcomes
        

    def visit_program(self, node: Program) -> None:
    
        for stmt in node.statements:
            t = stmt.type()
            
            if t in (NodeType.ClassStatement, NodeType.StructStatement):
                self.compile(stmt)

        
        for stmt in node.statements:
            t = stmt.type()
            if t not in (NodeType.ClassStatement, NodeType.StructStatement):
                self.compile(stmt)
        

    def visit_expression_statement(self, node: ExpressionStatement) -> None:
        if node.expr is not None:
            if isinstance(node.expr, StructStatement):
                self.visit_struct_definition_statement(node.expr)
            else:
                self.resolve_value(node.expr)
        
                
    def visit_var_statement(self, node: VarStatement) -> None:
        if node.name is None or not isinstance(node.name, IdentifierLiteral):
            raise ValueError("Variable name must be a non-null IdentifierLiteral")

        identifier = cast(IdentifierLiteral, node.name)
        if identifier.value is None:
            raise ValueError("Identifier name cannot be None")
        name: str = identifier.value
        if node.value is None:
            raise ValueError(f"Variable '{name}' has no assigned value.")

        value_expr: Expression = node.value
        value_type: Optional[str] = node.value_type

        if isinstance(value_expr, NullLiteral):
            ptr_type = ir.PointerType(ir.IntType(8))
            slot = self.builder.alloca(ptr_type, name=name)
            null_ptr = ir.Constant(ptr_type, None)
            self.builder.store(null_ptr, slot)
            self.env.define(name, slot, ptr_type)
            return

        resolved = self.resolve_value(value_expr, value_type)
        if resolved is None:
            raise ValueError(f"Failed to resolve value for variable '{name}'.")

        value_ir, ir_type = resolved

        if self.env.lookup(name) is not None:
            self.report_error(f"Variable '{name}' is already defined in this scope.")
            return

        if isinstance(ir_type, ir.PointerType) and isinstance(
            ir_type.pointee, ir.IdentifiedStructType # type: ignore
        ):  # type: ignore
            self.env.define(name, value_ir, ir_type)
            return

        if isinstance(ir_type, ir.PointerType) and isinstance(
            ir_type.pointee, ir.ArrayType # type: ignore
        ):  # type: ignore
            zero = ir.Constant(ir.IntType(32), 0)
            elem_ptr = self.builder.gep(value_ir, [zero, zero], inbounds=True, name=f"{name}_elem_ptr")
            slot = self.builder.alloca(elem_ptr.type, name=name)
            self.builder.store(elem_ptr, slot)

            self.array_lengths[name] = ir_type.pointee.count  # type: ignore

            self.env.define(name, slot, elem_ptr.type)
            return

        ptr = self.builder.alloca(ir_type, name=name)
        self.builder.store(value_ir, ptr)
        self.env.define(name, ptr, ir_type)
        if self.is_in_main:
           
            history_type = ir.ArrayType(ir_type, self.HISTORY_CAPACITY)
            history_ptr = self.builder.alloca(history_type, name=f"{name}_history")
            self.history_vars[name] = (history_ptr, ir_type)

            self._emit_save_state()   


    def visit_block_statement(self,node:BlockStatement)->None:
        for stmt in node.statements:
            self.compile(stmt)


    def visit_null_literal(self, node: NullLiteral) -> ir.Value:
        null_ptr_type = ir.IntType(32).as_pointer()
        return ir.Constant(null_ptr_type, None)


    def visit_return_statement(self, node: ReturnStatement) -> None:
        if node.return_value is None:
            self.builder.ret_void()
            return 

        expr = node.return_value
        resolved = self.resolve_value(expr)

        if resolved is None:
            raise ValueError("Failed to resolve return expression")

        value, typ = resolved
        self.builder.ret(value)


    def visit_function_statement(self, node: FunctionStatement) -> None:
        if node.name is None or node.name.value is None:
            raise ValueError("Function name is missing or invalid")
        name: str = node.name.value

        if node.body is None:
            raise ValueError(f"Function '{name}' has no body")
        body: BlockStatement = node.body

        params: list[FunctionParameter] = node.parameters or []
        param_names: list[str] = []
        param_types: list[ir.Type] = []

        for param in params:
            if param.name is None:
                raise ValueError(f"Function '{name}' has a parameter with no name")
            param_names.append(param.name)

            if param.value_type in self.type_map:
                param_types.append(self.type_map[param.value_type])
                
            elif param.value_type == "array":
    
                param_types.append(ir.IntType(32).as_pointer())
            else:
                param_types.append(ir.IntType(32))  
                
   
        func_type = ir.FunctionType(ir.VoidType(), param_types)
        dummy_module = ir.Module(name=f"{name}_dummy_module")
        dummy_func = ir.Function(dummy_module, func_type, name=f"{name}_dummy_temp")
        dummy_block = dummy_func.append_basic_block("entry")


        previous_module = self.module
        previous_builder = self.builder
        previous_env = self.env

        self.module = dummy_module
        self.builder = ir.IRBuilder(dummy_block)
        self.env = Environment(parent=self.env)
        
        self.env.define(name, dummy_func, ir.VoidType()) 
        
        for i, param_name in enumerate(param_names):
            dummy_ptr = self.builder.alloca(param_types[i])
            self.env.define(param_name, dummy_ptr, param_types[i])

        self.compile(body)
        
        
        if node.return_type is None:
            inferred_type: str | None = None
            for stmt in body.statements:
                if isinstance(stmt, ReturnStatement) and stmt.return_value is not None:
                    result = self.resolve_value(stmt.return_value)
                    if result is not None:
                        _, inferred_ir_type = result
                        if isinstance(inferred_ir_type, ir.IntType) and inferred_ir_type.width == 1:
                            inferred_type = "bool"
                        elif isinstance(inferred_ir_type, ir.IntType):
                            inferred_type = "int"
                        elif isinstance(inferred_ir_type, ir.FloatType):
                            inferred_type = "float"
                        elif isinstance(inferred_ir_type, ir.PointerType):
                            inferred_type = "array"
                        break
            if inferred_type is None:
                inferred_type = "void"
            ret_type_str = inferred_type
            
        else:
            ret_type_str = node.return_type

        node.return_type=ret_type_str
        self.module = previous_module
        self.builder = previous_builder
        self.env = previous_env

        if ret_type_str not in self.type_map:
            if ret_type_str == "array":
                return_ir_type = ir.IntType(32).as_pointer()
            else:
                raise ValueError(f"Unknown return type: {ret_type_str}")
        else:
            return_ir_type = self.type_map[ret_type_str]

    

        func = ir.Function(self.module, ir.FunctionType(return_ir_type, param_types), name=name)


        self.env.define(name, func, return_ir_type)

        block = func.append_basic_block(f'{name}_entry')
        previous_builder = self.builder
        self.builder = ir.IRBuilder(block)

        function_env = Environment(parent=self.env, name=name)
        previous_env = self.env
        self.env = function_env

        if name == "main":
            self.is_in_main = True
            time_func_res = self.env.lookup('time')
            srand_func_res = self.env.lookup('srand')
            if time_func_res and srand_func_res:
                time_func, _ = time_func_res
                srand_func, _ = srand_func_res
                
                null_ptr = ir.Constant(ir.IntType(32).as_pointer(), None)
                time_val = self.builder.call(time_func, [null_ptr], 'time_seed')
               
                self.builder.call(srand_func, [time_val])

            self.history_vars = {}
            self.history_idx_ptr = self.builder.alloca(ir.IntType(32), name="history_idx")
            self.history_len_ptr = self.builder.alloca(ir.IntType(32), name="history_len")
            self.builder.store(ir.Constant(ir.IntType(32), -1), self.history_idx_ptr)
            self.builder.store(ir.Constant(ir.IntType(32), 0), self.history_len_ptr)

        params_ptr = []
        for i, param_name in enumerate(param_names):
            ptr = self.builder.alloca(param_types[i], name=param_name)
            self.builder.store(func.args[i], ptr)
            self.env.define(param_name, ptr, param_types[i])

        
        

        self.compile(body)

        if ret_type_str == "void" and not any(isinstance(stmt, ReturnStatement) for stmt in body.statements):
            self.builder.ret_void()

        if name == "main":
            self.is_in_main = False 

    
        self.builder = previous_builder
        self.env=previous_env


    def visit_assign_statement(self, node: AssignStatement) -> None:
        if isinstance(node.ident, IdentifierLiteral):
            name = node.ident.value
            operator: str = node.operator

            if node.right_value is None:
                self.errors.append(
                    f"COMPILE ERROR: Assignment to '{name}' is missing a right-hand side expression"
                )
                return

            result = self.resolve_value(node.right_value)
            if result is None:
                self.errors.append(
                    f"COMPILE ERROR: Cannot resolve right-hand side of assignment to '{name}'"
                )
                return

            right_value, right_type = result

            if name is None:
                self.errors.append("COMPILE ERROR: Identifier name is missing")
                return

            entry = self.env.lookup(name)
            if entry is None:
                self.errors.append(f"COMPILE ERROR: Identifier '{name}' has not been declared")
                return

            ptr, var_type = entry
            if ptr is None:
                self.errors.append(f"COMPILE ERROR: No memory pointer for variable '{name}'")
                return

            orig_val = self.builder.load(ptr)
            if orig_val is None:
                self.errors.append(f"COMPILE ERROR: Failed to load value for variable '{name}'")
                return

            if isinstance(orig_val.type, ir.FloatType) and isinstance(right_type, ir.IntType):
                right_value = self.builder.sitofp(right_value, ir.FloatType())
            elif isinstance(orig_val.type, ir.IntType) and isinstance(right_type, ir.FloatType):
                orig_val = self.builder.sitofp(orig_val, ir.FloatType())

            value = None
            match operator:
                case '=':
                    value = right_value

                case '+=':
                    if orig_val is not None and isinstance(orig_val.type, ir.IntType):
                        value = self.builder.add(orig_val, right_value)
                    elif orig_val is not None:
                        value = self.builder.fadd(orig_val, right_value)
                    else:
                        self.errors.append("COMPILE ERROR: Cannot perform '+=' on undefined variable")
                        return

                case '-=':
                    if orig_val is not None and isinstance(orig_val.type, ir.IntType):
                        value = self.builder.sub(orig_val, right_value)
                    elif orig_val is not None:
                        value = self.builder.fsub(orig_val, right_value)
                    else:
                        self.errors.append("COMPILE ERROR: Cannot perform '-=' on undefined variable")
                        return

                case '*=':
                    if orig_val is not None and isinstance(orig_val.type, ir.IntType):
                        value = self.builder.mul(orig_val, right_value)
                    elif orig_val is not None:
                        value = self.builder.fmul(orig_val, right_value)
                    else:
                        self.errors.append("COMPILE ERROR: Cannot perform '*=' on undefined variable")
                        return

                case '/=':
                    if orig_val is not None and isinstance(orig_val.type, ir.IntType):
                        value = self.builder.sdiv(orig_val, right_value)
                    elif orig_val is not None:
                        value = self.builder.fdiv(orig_val, right_value)
                    else:
                        self.errors.append("COMPILE ERROR: Cannot perform '/=' on undefined variable")
                        return

                case _:
                    self.errors.append(f"COMPILE ERROR: Unsupported assignment operator '{operator}'")
                    return

            self.builder.store(value, ptr)
            if self.is_in_main:
                self._emit_save_state()

        elif isinstance(node.ident, StructAccessExpression):
            
            member_access_node = cast(StructAccessExpression, node.ident)
            member_name = member_access_node.member_name.value
            if member_name is None:
                return self.report_error("Member assignment missing name.")

            obj_resolved = self.resolve_value(member_access_node.struct_name)
            if obj_resolved is None:
                return self.report_error("Could not resolve object in member assignment.")
            obj_ptr, obj_type = obj_resolved

            if not isinstance(obj_type, ir.PointerType) or not isinstance(
                obj_type.pointee, ir.IdentifiedStructType # type: ignore
            ):  # type: ignore
                return self.report_error("Member assignment requires a struct instance.")

            struct_type = cast(ir.IdentifiedStructType, obj_type.pointee)  # type: ignore
            struct_name = struct_type.name
            layout = self.struct_layouts.get(struct_name)
            member_index = layout.get(member_name) if layout else None
            if member_index is None:
                return self.report_error(f"Struct '{struct_name}' has no member '{member_name}'.")

            if node.right_value is None:
                return self.report_error("Assignment is missing a value.")
            right_resolved = self.resolve_value(node.right_value)
            if right_resolved is None:
                return self.report_error("Could not resolve assignment value.")
            value_to_store, _ = right_resolved

          
            zero = ir.Constant(ir.IntType(32), 0)
            member_ptr = self.builder.gep(
                obj_ptr, [zero, ir.Constant(ir.IntType(32), member_index)], inbounds=True
            )
            self.builder.store(value_to_store, member_ptr)
            return

        elif isinstance(node.ident, DerefExpression):
            
            deref_node = cast(DerefExpression, node.ident)
            pointer_result = self.resolve_value(deref_node.pointer_expression)
            if pointer_result is None:
                self.report_error("Cannot resolve pointer on the left side of assignment.")
                return

            target_ptr, _ = pointer_result

            if node.right_value is None:
                self.report_error("Assignment is missing a right-hand side expression")
                return

            right_result = self.resolve_value(node.right_value)
            if right_result is None:
                self.report_error("Cannot resolve right-hand side of assignment.")
                return

            value_to_store, _ = right_result

            self.builder.store(value_to_store, target_ptr)
            return

        elif isinstance(node.ident, ArrayAccessExpression):
            array_result = self.resolve_value(node.ident.array)
            if array_result is None:
                self.errors.append("COMPILE ERROR: Cannot resolve array in assignment")
                return
            array_val, array_type = array_result

            index_result = self.resolve_value(node.ident.index)
            if index_result is None:
                self.errors.append("COMPILE ERROR: Cannot resolve index in array assignment")
                return
            index_val, index_type = index_result

            if node.right_value is None:
                self.errors.append(
                    "COMPILE ERROR: Assignment to array element missing right-hand side expression"
                )
                return

            right_result = self.resolve_value(node.right_value)
            if right_result is None:
                self.errors.append(
                    "COMPILE ERROR: Cannot resolve right-hand side value in array assignment"
                )
                return
            right_value, right_type = right_result

            if isinstance(array_type, ir.PointerType) and isinstance(array_type.pointee, ir.ArrayType):  # type: ignore
                elem_ptr = self.builder.gep(
                    array_val,
                    [ir.Constant(ir.IntType(32), 0), index_val],
                    inbounds=True,
                    name="array_elem_ptr",
                )
                elem_type = array_type.pointee.element  # type: ignore
            elif isinstance(array_type, ir.PointerType) and isinstance(array_type.pointee, ir.IntType):  # type: ignore
                elem_ptr = self.builder.gep(
                    array_val,
                    [index_val],
                    inbounds=True,
                    name="array_elem_ptr",
                )
                elem_type = array_type.pointee  # type: ignore
            else:
                self.errors.append(
                    "COMPILE ERROR: Cannot index into non-array type in assignment"
                )
                return

            if elem_type != right_type:
                if isinstance(elem_type, ir.FloatType) and isinstance(right_type, ir.IntType):
                    right_value = self.builder.sitofp(right_value, elem_type)
                elif isinstance(elem_type, ir.IntType) and isinstance(right_type, ir.FloatType):
                    right_value = self.builder.fptosi(right_value, elem_type)
                else:
                    self.errors.append("COMPILE ERROR: Type mismatch in array assignment")
                    return

            self.builder.store(right_value, elem_ptr)
            if self.is_in_main:
                self._emit_save_state()

        else:
            self.errors.append(
                "COMPILE ERROR: Left-hand side of assignment must be an identifier or array element"
            )
            return
    

    def _emit_save_state(self):
        
        if not self.is_in_main or not self.history_idx_ptr or not self.history_len_ptr:
            return

        current_idx_val = self.builder.load(self.history_idx_ptr, name="current_idx")
        next_idx_val = self.builder.add(current_idx_val, ir.Constant(ir.IntType(32), 1), name="next_idx")

        for name, (history_ptr, _) in self.history_vars.items():
            var_entry = self.env.lookup(name)
            if var_entry:
                var_ptr, _ = var_entry
                current_val = self.builder.load(var_ptr)
                
                target_slot_ptr = self.builder.gep(history_ptr, 
                                                [ir.Constant(ir.IntType(32), 0), next_idx_val], 
                                                inbounds=True, name=f"{name}_history_slot")
                self.builder.store(current_val, target_slot_ptr)

      
        self.builder.store(next_idx_val, self.history_idx_ptr)
        new_len_val = self.builder.add(next_idx_val, ir.Constant(ir.IntType(32), 1), name="new_history_len")
        self.builder.store(new_len_val, self.history_len_ptr)


    def _emit_restore_state(self, target_idx_val: ir.Value):
       
        if not self.is_in_main:
            return


        for name, (history_ptr, _) in self.history_vars.items():
            var_entry = self.env.lookup(name)
            if var_entry:
                var_ptr, _ = var_entry
                
                source_slot_ptr = self.builder.gep(history_ptr, 
                                                [ir.Constant(ir.IntType(32), 0), target_idx_val], 
                                                inbounds=True, name=f"{name}_historic_slot")
                historic_val = self.builder.load(source_slot_ptr, name=f"{name}_historic_val")
                self.builder.store(historic_val, var_ptr)
  

    def visit_rewind_statement(self, node: RewindStatement) -> None:
        if not self.is_in_main or not self.history_idx_ptr or not self.history_len_ptr:
            self.report_error("'rewind' can only be used inside the 'main' function.")
            return

        steps_res = self.resolve_value(node.steps)
        if steps_res is None:
            self.report_error("Invalid steps for rewind.")
            return
        steps_val, _ = steps_res

        current_idx_val = self.builder.load(self.history_idx_ptr, name="current_idx")
        target_idx_val = self.builder.sub(current_idx_val, steps_val, name="rewind_target_idx")

        is_neg = self.builder.icmp_signed('<', target_idx_val, ir.Constant(ir.IntType(32), 0))
        clamped_idx = self.builder.select(is_neg, ir.Constant(ir.IntType(32), 0), target_idx_val, name="clamped_rewind_idx")

        self._emit_restore_state(clamped_idx)
        self.builder.store(clamped_idx, self.history_idx_ptr)
       

    def visit_fastforward_statement(self, node: FastForwardStatement) -> None:
        if not self.is_in_main or not self.history_idx_ptr or not self.history_len_ptr:
            self.report_error("'fastforward' can only be used inside the 'main' function.")
            return

        steps_res = self.resolve_value(node.steps)
        if steps_res is None:
            self.report_error("Invalid steps for fastforward.")
            return
        steps_val, _ = steps_res

        current_idx_val = self.builder.load(self.history_idx_ptr, name="current_idx")
        history_len_val = self.builder.load(self.history_len_ptr, name="history_len")

        has_any = self.builder.icmp_signed('>', history_len_val, ir.Constant(ir.IntType(32), 0))
        with self.builder.if_then(has_any):
            max_idx = self.builder.sub(history_len_val, ir.Constant(ir.IntType(32), 1), name="max_idx")
            target_idx_val = self.builder.add(current_idx_val, steps_val, name="ff_target_idx")

            too_far = self.builder.icmp_signed('>', target_idx_val, max_idx)
            clamped_idx = self.builder.select(too_far, max_idx, target_idx_val, name="clamped_ff_idx")
            self._emit_restore_state(clamped_idx)
            self.builder.store(clamped_idx, self.history_idx_ptr)
        


    def visit_break_statement(self, node: BreakStatement) -> None:
        if not self.breakpoints:
            self.report_error("Invalid 'break' used outside of a loop.")
            return

        target_block = self.breakpoints[-1]
        self.builder.branch(target_block)

        dummy_block = self.builder.append_basic_block(name="after_break")
        self.builder.position_at_start(dummy_block)


    def visit_continue_statement(self, node: ContinueStatement) -> None:
        if not self.continues:
            self.report_error("Invalid 'continue' used outside of a loop.")
            return

    
        target_block = self.continues[-1]
        self.builder.branch(target_block)

        dummy_block = self.builder.append_basic_block(name="after_continue")
        self.builder.position_at_start(dummy_block)


    def report_error(self, message: str) -> None:
        self.errors.append(message)
    

    def visit_if_statement(self, node: IfStatement) -> None:
        if node.condition is None:
            self.report_error("If condition is missing.")
            return

        result = self.resolve_value(node.condition)
        if result is None:
            self.report_error("Failed to resolve condition in if-statement")
            return

        test, _ = result

        # This check handles a simple 'if...fi' with no 'else' or 'elif'
        if node.alternative is None and node.el_if is None:
            with self.builder.if_then(test):
                if node.consequence is not None:
                    self.compile(node.consequence)
        else:
            # This handles both 'if...else' and 'if...elif'
            with self.builder.if_else(test) as (then_block, else_block):
                # First, compile the consequence for the 'if' part
                with then_block:
                    if node.consequence is not None:
                        self.compile(node.consequence)
                
                # Next, position the builder in the 'else' block
                with else_block:
                    # If an 'el_if' exists, compile it. This will recursively
                    # call visit_if_statement for the next link in the chain.
                    if node.el_if is not None:
                        self.compile(node.el_if)
                    # Otherwise, if it's a simple 'else', compile the alternative block.
                    elif node.alternative is not None:
                        self.compile(node.alternative)
                        

    def visit_while_statement(self, node: WhileStatement) -> None:
        condition: Expression = node.condition
        body: BlockStatement = node.body

        while_loop_test = self.builder.append_basic_block(f"while_loop_test_{self.increment_counter()}")
        while_loop_body = self.builder.append_basic_block(f"while_loop_body_{self.counter}")
        while_loop_exit = self.builder.append_basic_block(f"while_loop_exit_{self.counter}")

        self.builder.branch(while_loop_test)

        self.builder.position_at_start(while_loop_test)
        result = self.resolve_value(condition)
        if result is None:
            self.report_error("Failed to resolve condition in while statement")
            return
        test, _ = result
        self.builder.cbranch(test, while_loop_body, while_loop_exit)

    
        self.builder.position_at_start(while_loop_body)

    
        self.breakpoints.append(while_loop_exit)

        self.compile(body)

        self.breakpoints.pop()

        self.builder.branch(while_loop_test)
        
        self.builder.position_at_start(while_loop_exit)


    def visit_load_statement(self,node:LoadStatement)->None:
        file_path:str=node.file_path

        if not file_path.endswith(".hal"):
            file_path += ".hal"

        if self.global_parsed_pallets.get(file_path) is not None:
            print(f"Hal warns: {file_path} is already imported globally\n")
            return
        

        if file_path in BUILTIN_HEADERS:
            pallet_code = BUILTIN_HEADERS[file_path]
        else:
            search_paths = [
                os.path.abspath(f"headers/{file_path}"),
                os.path.abspath(f"tests/{file_path}")
            ]
            full_path = next((p for p in search_paths if os.path.exists(p)), None)
            if not full_path:
                raise FileNotFoundError(f"Module '{file_path}' not found in built-ins, headers/, or tests/")
            with open(full_path, "r") as f:
                pallet_code = f.read()

        l:Lexer=Lexer(source=pallet_code)
        p:Parser=Parser(lexer=l)
        program:Program=p.parse_program()
        if len(p.errors)>0:
            print(f"error with imported pallet:{file_path}")
            for err in p.errors:
                print(err)
            exit(1)
        self.compile(node=program)
        self.global_parsed_pallets[file_path]=program


    """def visit_while_statement(self,node:WhileStatement)->None:
        condition:Expression=node.condition
        body:BlockStatement=node.body
        result=self.resolve_value(condition)
        if result is None:
            self.report_error("failed to resolve condition in while statment")
            return
        test,_=result
        while_loop_entry=self.builder.append_basic_block(f"while_loop_entry_{self.increment_counter()}")
        while_loop_otherwise=self.builder.append_basic_block(f"while_loop_otherwise_{self.counter}")
        
        self.builder.cbranch(test,while_loop_entry,while_loop_otherwise)
        self.builder.position_at_start(while_loop_entry)
        self.compile(body)
        res=self.resolve_value(condition)
        if res is None:
            self.report_error("failed to resolve condition in while statment")
            return
        test,_=res
        self.builder.cbranch(test,while_loop_entry,while_loop_otherwise)

        self.builder.position_at_start(while_loop_otherwise)"""

   
    def visit_infix_expression(self, node: InfixExpression) -> tuple[ir.Value, ir.Type] | None:
        operator: str = node.operator

        if node.left_node is None or node.right_node is None:
            self.report_error("InfixExpression is missing left or right operand.")
            return None

        left_result = self.resolve_value(node.left_node)
        right_result = self.resolve_value(node.right_node)
    

        if left_result is None or right_result is None:
            self.report_error("Failed to resolve left or right value.")
            return None
        

        left_value, left_type = left_result
        right_value, right_type = right_result

        if isinstance(left_type, ir.DoubleType) or isinstance(right_type, ir.DoubleType):
            if not isinstance(left_type, ir.DoubleType):
                left_value = self.builder.fpext(left_value, ir.DoubleType()) if isinstance(left_type, ir.FloatType) else self.builder.sitofp(left_value, ir.DoubleType())
                left_type = ir.DoubleType()
            if not isinstance(right_type, ir.DoubleType):
                right_value = self.builder.fpext(right_value, ir.DoubleType()) if isinstance(right_type, ir.FloatType) else self.builder.sitofp(right_value, ir.DoubleType())
                right_type = ir.DoubleType()

        if isinstance(left_type, ir.FloatType) and isinstance(right_type, ir.IntType):
            right_value = self.builder.sitofp(right_value, ir.FloatType(), name="promoted_int_to_float")
            right_type = ir.FloatType()
        elif isinstance(left_type, ir.IntType) and isinstance(right_type, ir.FloatType):
            left_value = self.builder.sitofp(left_value, ir.FloatType(), name="promoted_int_to_float")
            left_type = ir.FloatType()



        value = None
        Type = None

        if operator == '&&':
            value = self.builder.and_(left_value, right_value, name='and_res')
            Type = ir.IntType(1)
            if value is None:
                self.report_error("Failed to build 'and' operation")
                return None
            return value, Type
        
        if operator == '||':
            value = self.builder.or_(left_value, right_value, name='or_res')
            Type = ir.IntType(1)
            if value is None:
                self.report_error("Failed to build 'and' operation")
                return None
            return value, Type

        if isinstance(left_type, ir.PointerType) and isinstance(right_type, ir.IntType):
            Type = left_type 
            if operator == '+':
               
                value = self.builder.gep(left_value, [right_value], inbounds=True, name="ptr_add")
            elif operator == '-':
               
                neg_right_value = self.builder.neg(right_value, name="ptr_sub_idx")
                value = self.builder.gep(left_value, [neg_right_value], inbounds=True, name="ptr_sub")
        elif isinstance(left_type, ir.IntType) and isinstance(right_type, ir.PointerType):
             Type = right_type
             if operator == '+':
                value = self.builder.gep(right_value, [left_value], inbounds=True, name="ptr_add")

        if node.operator in ("==", "!="):
            
            if isinstance(left_type, ir.PointerType) and isinstance(right_value, ir.Constant) and right_value.constant is None:
                cmp_val: ir.Instruction = self.builder.icmp_unsigned("==", left_value, right_value, name="null_cmp_eq")
                if cmp_val is None:
                    self.report_error("Failed to build null comparison")
                    return None
                if node.operator == "!=":
                    self.builder.not_(cmp_val, name="null_cmp_neq")
                return cmp_val, ir.IntType(1)

            
            if isinstance(right_type, ir.PointerType) and isinstance(left_value, ir.Constant) and left_value.constant is None:
                cmp_val: ir.Instruction = self.builder.icmp_unsigned("==", right_value,left_value, name="null_cmp_eq")
                if cmp_val is None:
                    self.report_error("Failed to build null comparison")
                    return None
                if node.operator == "!=":
                    self.builder.not_(cmp_val, name="null_cmp_neq")
                return cmp_val, ir.IntType(1)


        


        
        
        if isinstance(left_type, ir.IntType) and isinstance(right_type, ir.IntType):
            Type = self.type_map['int']
            match operator:
                case '+':
                    value = self.builder.add(left_value, right_value)
                case '-':
                    value = self.builder.sub(left_value, right_value)
                case '*':
                    value = self.builder.mul(left_value, right_value)
                case '/':
                    value = self.builder.sdiv(left_value, right_value)
                case '%':
                    value = self.builder.srem(left_value, right_value)
                case '^':
                    
                    pass
                case '<':
                    value = self.builder.icmp_signed('<',left_value, right_value)
                    Type=ir.IntType(1) 
                case '<=':
                    value = self.builder.icmp_signed('<=',left_value, right_value)
                    Type=ir.IntType(1) 
                case '>':
                    value = self.builder.icmp_signed('>',left_value, right_value)
                    Type=ir.IntType(1) 
                case '>=':
                    value = self.builder.icmp_signed('>=',left_value, right_value)
                    Type=ir.IntType(1) 
                case '==':
                    value = self.builder.icmp_signed('==',left_value, right_value)
                    Type=ir.IntType(1) 
                case '!=':
                    value = self.builder.icmp_signed('!=',left_value, right_value)
                    Type=ir.IntType(1) 
                
        elif isinstance(right_type,ir.DoubleType) and isinstance(left_type,ir.DoubleType):
            Type=ir.DoubleType()
            match operator:
                case '+':
                    value=self.builder.fadd(left_value,right_value)
                case '-':
                    value=self.builder.fsub(left_value,right_value)
                case '*':
                    value=self.builder.fmul(left_value,right_value)
                case '/':
                    value=self.builder.fdiv(left_value,right_value)

        elif isinstance(right_type,ir.FloatType) and isinstance(left_type,ir.FloatType):
            Type=ir.FloatType()
            match operator:
                case '+':
                    value=self.builder.fadd(left_value,right_value)
                case '-':
                    value=self.builder.fsub(left_value,right_value)
                case '*':
                    value=self.builder.fmul(left_value,right_value)
                case '/':
                    value=self.builder.fdiv(left_value,right_value)
                case '%':
                    value=self.builder.frem(left_value,right_value)
                case '^':
                    
                    pass
                case '<':
                    value = self.builder.fcmp_ordered('<',left_value, right_value)
                    Type=ir.IntType(1) 
                case '<=':
                    value = self.builder.fcmp_ordered('<=',left_value, right_value)
                    Type=ir.IntType(1) 
                case '>':
                    value = self.builder.fcmp_ordered('>',left_value, right_value)
                    Type=ir.IntType(1) 
                case '>=':
                    value = self.builder.fcmp_ordered('>=',left_value, right_value)
                    Type=ir.IntType(1) 
                case '==':
                    value = self.builder.fcmp_ordered('==',left_value, right_value)
                    Type=ir.IntType(1)
                case '!=':
                    value = self.builder.fcmp_ordered('!=',left_value, right_value)
                    Type=ir.IntType(1) 

        if value is not None and Type is not None:
            return value, Type

        self.report_error(f"Unsupported operator '{operator}' or incompatible operand types.")
        return None


    def handle_H_call(self, args: list) -> None:
        if len(args) != 1:
            self.report_error("H requires exactly 1 qubit argument")
            return

        node = args[0]
        if not isinstance(node, IdentifierLiteral):
            self.report_error("H argument must be a qubit identifier")
            return

        name = node.value
        if name not in self.qubits:
            self.report_error(f"Qubit '{name}' not declared")
            return

       
        q = self.qubits[name]
        a, b = q.get("alpha", 1.0), q.get("beta", 0.0)
        q["alpha"] = (a + b) / math.sqrt(2)
        q["beta"] = (a - b) / math.sqrt(2)
        q["superposition"] = True
        

    def handle_CNOT_call(self, args: list) -> None:
        if len(args) != 2:
            self.report_error("CNOT requires exactly two qubits")
            return

        control_expr, target_expr = args
        if not isinstance(control_expr, IdentifierLiteral) or not isinstance(target_expr, IdentifierLiteral):
            self.report_error("CNOT arguments must be qubit identifiers")
            return

        control = control_expr.value
        target = target_expr.value

        if control not in self.qubits or target not in self.qubits:
            self.report_error("Both qubits must be declared")
            return

        control_q = self.qubits[control]
        target_q = self.qubits[target]

        if control_q.get("superposition", False):
            p0 = abs(control_q["alpha"]) ** 2
            collapsed = 0 if random.random() < p0 else 1
            control_q["state"] = collapsed
            control_q["alpha"], control_q["beta"] = (1.0, 0.0) if collapsed == 0 else (0.0, 1.0)
            control_q["superposition"] = False

       
        if control_q["state"] == 1:
            target_q["state"] = 1 - target_q["state"]
           
            if target_q.get("superposition", False):
                target_q["alpha"], target_q["beta"] = (1.0, 0.0) if target_q["state"] == 0 else (0.0, 1.0)
                target_q["superposition"] = False


    def visit_qubit_declaration(self, node: QubitDeclarationStatement) -> None:
       
        if not isinstance(node.name, IdentifierLiteral) or node.name.value is None:
            return self.report_error("Qubit name must be a valid identifier")

        name = node.name.value
        if name in self.qubits:
            return self.report_error(f"Qubit '{name}' already declared.")

        initial_state_val = node.initial_state.value if node.initial_state else 0

        func = self.builder.function
        entry_block = func.entry_basic_block

        entry_builder = ir.IRBuilder(entry_block)
        if entry_block.instructions:
            entry_builder.position_before(entry_block.instructions[0])
        else:
            entry_builder.position_at_end(entry_block)

        qubit_alloca = entry_builder.alloca(ir.IntType(32), name=name)
        print("Allocated qubit:", name, "->", qubit_alloca)
        entry_builder.store(ir.Constant(ir.IntType(32), initial_state_val), qubit_alloca)

        self.qubits[name] = {
            "alloca": qubit_alloca,
            "state": initial_state_val,
            "superposition": False,
            "alpha": 1.0 if initial_state_val == 0 else 0.0,
            "beta": 0.0 if initial_state_val == 0 else 1.0,
        }


    def visit_qubit_reset(self, node: QubitResetStatement) -> None:
       
        if not isinstance(node.name, IdentifierLiteral) or node.name.value is None:
            return self.report_error("Qubit name for reset must be a valid identifier")

        name = node.name.value
        if name not in self.qubits:
            return self.report_error(f"Cannot reset undeclared qubit '{name}'.")

        target_state = node.initial_state.value if node.initial_state else 0

        
        qubit_sim_state = self.qubits[name]
        qubit_sim_state["state"] = target_state
        qubit_sim_state["superposition"] = False
        qubit_sim_state["alpha"] = 1.0 if target_state == 0 else 0.0
        qubit_sim_state["beta"] = 0.0 if target_state == 0 else 1.0

        qubit_alloca = qubit_sim_state["alloca"]
        parent_block = qubit_alloca.parent
        entry_builder = ir.IRBuilder(parent_block)
        entry_builder.store(ir.Constant(ir.IntType(32), target_state), qubit_alloca)


    def handle_X_call(self, args: list) -> None:
        if len(args) != 1:
            self.report_error("X requires exactly one qubit")
            return

        node = args[0]
        if not isinstance(node, IdentifierLiteral):
            self.report_error("X argument must be a qubit identifier")
            return

        name = node.value
        if name not in self.qubits:
            self.report_error(f"Qubit '{name}' not declared")
            return

        q = self.qubits[name]
        
        q["alpha"], q["beta"] = q["beta"], q["alpha"]
        
        if not q["superposition"]:
            q["state"] = 1 - q["state"]

        
    def visit_measure_expression(self, node: MeasureExpression) -> tuple[ir.Value, ir.Type] | None:
        target_name = node.target.value
        if target_name not in self.qubits:
            self.report_error(f"Cannot measure undeclared qubit '{target_name}'.")
            return None

        q = self.qubits[target_name]

        if q.get("superposition", False):
          
            p0 = abs(q["alpha"]) ** 2
            result = 0 if random.random() < p0 else 1
            q["state"] = result
            q["alpha"], q["beta"] = (1.0, 0.0) if result == 0 else (0.0, 1.0)
            q["superposition"] = False
        else:
            result = q["state"]

        llvm_val = ir.Constant(ir.IntType(32), result)
        llvm_type = ir.IntType(32)
        return llvm_val, llvm_type


    def handle_SWAP_call(self, args: list) -> None:
        if len(args) != 2:
            self.report_error("SWAP requires exactly two qubits.")
            return

        q1_expr, q2_expr = args
        if not isinstance(q1_expr, IdentifierLiteral) or not isinstance(q2_expr, IdentifierLiteral):
            self.report_error("SWAP arguments must be qubit identifiers.")
            return

        q1_name = q1_expr.value
        q2_name = q2_expr.value

        if q1_name not in self.qubits or q2_name not in self.qubits:
            self.report_error("Both qubits must be declared for SWAP.")
            return

        q1 = self.qubits[q1_name]
        q2 = self.qubits[q2_name]

        
        q1["state"], q2["state"] = q2["state"], q1["state"]

        q1["superposition"], q2["superposition"] = q2["superposition"], q1["superposition"]

      
        q1["alpha"], q2["alpha"] = q2["alpha"], q1["alpha"]
        q1["beta"], q2["beta"] = q2["beta"], q1["beta"]



    def handle_S_call(self, args: list) -> None:
        if len(args) != 1:
            self.report_error("S gate requires exactly one qubit argument.")
            return

        node = args[0]
        if not isinstance(node, IdentifierLiteral):
            self.report_error("S gate argument must be a qubit identifier.")
            return

        name = node.value
        if name not in self.qubits:
            self.report_error(f"Qubit '{name}' not declared.")
            return

        q = self.qubits[name]

        
        alpha, beta = q.get("alpha", 1.0), q.get("beta", 0.0)
        q["alpha"] = alpha 
        q["beta"] = complex(0, 1) * beta  


    def handle_CZ_call(self, args: list) -> None:
        if len(args) != 2:
            self.report_error("CZ requires exactly two qubits")
            return

        control_expr, target_expr = args
        if not isinstance(control_expr, IdentifierLiteral) or not isinstance(target_expr, IdentifierLiteral):
            self.report_error("CZ arguments must be qubit identifiers")
            return

        control = control_expr.value
        target = target_expr.value

        if control not in self.qubits or target not in self.qubits:
            self.report_error("Both qubits must be declared")
            return

        control_q = self.qubits[control]
        target_q = self.qubits[target]

        
        if control_q.get("superposition", False):
            control_q["state"] = random.choice([0, 1])
            control_q["superposition"] = False

        
        if control_q["state"] == 1:
    
            target_q["beta"] = -target_q.get("beta", 0.0)

       
    def handle_T_call(self, args: list) -> None:
        if len(args) != 1:
            self.report_error("T gate requires exactly one qubit argument.")
            return

        node = args[0]
        if not isinstance(node, IdentifierLiteral):
            self.report_error("T gate argument must be a qubit identifier.")
            return

        name = node.value
        if name not in self.qubits:
            self.report_error(f"Qubit '{name}' not declared.")
            return

        q = self.qubits[name]
        a, b = q.get("alpha", 1.0), q.get("beta", 0.0)

        
        q["alpha"] = a
        q["beta"] = b * cmath.exp(1j * cmath.pi / 4)

        
        q["superposition"] = not (q["alpha"] in [0, 1] and q["beta"] in [0, 1])

        
    def handle_Tdg_call(self, args: list) -> None:
        if len(args) != 1:
            self.report_error("Tdg gate requires exactly one qubit argument.")
            return

        node = args[0]
        if not isinstance(node, IdentifierLiteral):
            self.report_error("Tdg argument must be a qubit identifier.")
            return

        name = node.value
        if name not in self.qubits:
            self.report_error(f"Qubit '{name}' not declared.")
            return

        q = self.qubits[name]

        
        a, b = q.get("alpha", 1.0), q.get("beta", 0.0)

       
        theta = -math.pi / 4
        new_a = a
        new_b = b * complex(math.cos(theta), math.sin(theta))

        q["alpha"] = new_a
        q["beta"] = new_b
        q["superposition"] = True 


    def handle_Sdg_call(self, args: list) -> None:
        if len(args) != 1:
            self.report_error("Sdg requires exactly one qubit argument.")
            return

        qubit_expr = args[0]
        if not isinstance(qubit_expr, IdentifierLiteral):
            self.report_error("Sdg argument must be a qubit identifier.")
            return

        qubit_name = qubit_expr.value
        if qubit_name not in self.qubits:
            self.report_error(f"Qubit '{qubit_name}' not declared.")
            return

        q = self.qubits[qubit_name]

        
        if not q["superposition"]:
            return  
        alpha, beta = q["alpha"], q["beta"]
      
        new_beta = complex(0, -1) * beta
        q["alpha"], q["beta"] = alpha, new_beta


    def handle_TOFFOLI_call(self, args: list) -> None:
        if len(args) != 3:
            self.report_error("TOFFOLI gate requires exactly three qubit arguments.")
            return

        ctrl1_expr, ctrl2_expr, target_expr = args
        for expr in [ctrl1_expr, ctrl2_expr, target_expr]:
            if not isinstance(expr, IdentifierLiteral):
                self.report_error("All TOFFOLI arguments must be qubit identifiers.")
                return

        ctrl1 = ctrl1_expr.value
        ctrl2 = ctrl2_expr.value
        target = target_expr.value

        if ctrl1 not in self.qubits or ctrl2 not in self.qubits or target not in self.qubits:
            self.report_error("All qubits in TOFFOLI must be declared.")
            return

        q1 = self.qubits[ctrl1]
        q2 = self.qubits[ctrl2]
        q3 = self.qubits[target]

       
        for q in [q1, q2]:
            if q["superposition"]:
                q["state"] = random.choice([0, 1])
                q["superposition"] = False

        
        if q1["state"] == 1 and q2["state"] == 1:
            if q3["superposition"]:
                
                q3["state"] = random.choice([0, 1])
                q3["superposition"] = False
        
            q3["state"] = 1 - q3["state"]


    def handle_CSWAP_call(self, args: list) -> None:
        
        if len(args) != 3:
            self.report_error("CSWAP requires exactly three qubits: control, target1, target2")
            return

        control_expr, t1_expr, t2_expr = args
        if not all(isinstance(e, IdentifierLiteral) for e in [control_expr, t1_expr, t2_expr]):
            self.report_error("All CSWAP arguments must be qubit identifiers")
            return

        control = control_expr.value
        t1 = t1_expr.value
        t2 = t2_expr.value

        if any(q not in self.qubits for q in [control, t1, t2]):
            self.report_error("All qubits in CSWAP must be declared")
            return

        c_q = self.qubits[control]
        q1 = self.qubits[t1]
        q2 = self.qubits[t2]

        
        if c_q["superposition"]:
            c_q["state"] = random.choice([0, 1])
            c_q["superposition"] = False

        if c_q["state"] == 1:
            q1["state"], q2["state"] = q2["state"], q1["state"]

        

    def visit_call_expression(self, node: CallExpression) -> tuple[ir.Value, ir.Type] | None:
        params: list[Expression] = node.arguments if node.arguments is not None else []
        if isinstance(node.function, StructAccessExpression):
            access_node = cast(StructAccessExpression, node.function)
            method_name = access_node.member_name.value
           
            instance_resolved = self.resolve_value(access_node.struct_name)
            if instance_resolved is None:
                return self.report_error("Could not resolve instance for method call.")
            instance_ptr, instance_type = instance_resolved
            
            if not (isinstance(instance_type, ir.PointerType) and isinstance(instance_type.pointee, ir.IdentifiedStructType)): # type: ignore
                return self.report_error("Method call on a non-class instance.")
            
            class_type = cast(ir.IdentifiedStructType, instance_type.pointee) # type: ignore
            class_name = class_type.name
            
            num_args = len(node.arguments) if node.arguments is not None else 0
            mangled_name = f"{class_name}_{method_name}_{num_args}"

            func_result = self.env.lookup(mangled_name)
            if func_result is None:
                return self.report_error(f"Class '{class_name}' has no method '{method_name}'.")
            
            func, ret_type = func_result
            func = cast(ir.Function, func)

            
            args_ir: list[ir.Value] = []
            for arg_expr in params:
                arg_resolved = self.resolve_value(arg_expr)
                if arg_resolved is None: return self.report_error("Could not resolve method argument.")
                args_ir.append(arg_resolved[0])
            
            final_args = [instance_ptr] + args_ir
            
            ret = self.builder.call(func, final_args)
            return ret, ret_type
        
        if not isinstance(node.function, IdentifierLiteral) or node.function.value is None:
            self.report_error("CallExpression function must be an identifier with a name.")
            return None
        name: str = node.function.value

        if name == "T":
            if node.arguments is None:
                self.report_error("T function requires a qubit argument.")
                return None
            self.handle_T_call(node.arguments)
            return None
        if name == "Tdg":
            if node.arguments is None:
                self.report_error("TDG function requires a qubit argument.")
                return None
            self.handle_Tdg_call(node.arguments)
            return None
        if name == "X":
            if node.arguments is None:
                self.report_error("X function requires a qubit argument.")
                return None
            self.handle_X_call(node.arguments)
            return None
        if name == "SWAP":
            if node.arguments is None:
                self.report_error("SWAP function requires a qubit argument.")
                return None
            self.handle_SWAP_call(node.arguments)
            return None
        if name == "CSWAP":
            if node.arguments is None:
                self.report_error("CSWAP function requires a qubit argument.")
                return None
            self.handle_CSWAP_call(node.arguments)
            return None
        if name == "TOFFOLI":
            if node.arguments is None:
                self.report_error("TOFFOLI function requires a qubit argument.")
                return None
            self.handle_TOFFOLI_call(node.arguments)
            return None
        if name == "CZ":
            if node.arguments is None:
                self.report_error("CZ function requires a qubit argument.")
                return None
            self.handle_CZ_call(node.arguments)
            return None
        if name == "S":
            if node.arguments is None:
                self.report_error("S function requires a qubit argument.")
                return None
            self.handle_S_call(node.arguments)
            return None
        
        if name == "Sdg":
            if node.arguments is None:
                self.report_error("SDG function requires a qubit argument.")
                return None
            self.handle_Sdg_call(node.arguments)
            return None
        
        if name == "H":
            if node.arguments is None:
                self.report_error("H function requires a qubit argument.")
                return None
            self.handle_H_call(node.arguments)
            return None 
        
        elif name == "CNOT":
            if node.arguments is None:
                self.report_error("CNOT function requires a qubit argument.")
                return None
            self.handle_CNOT_call(node.arguments)
            return None
        
        if name in self.struct_types:
            args_ir: list[ir.Value] = []
            for arg_expr in params:
                arg_resolved = self.resolve_value(arg_expr)
                if arg_resolved is None:
                    return self.report_error("Failed to resolve constructor argument.")
                args_ir.append(arg_resolved[0])
            
            struct_type = self.struct_types[name]
            ptr = self.builder.alloca(struct_type, name=f"{name.lower()}_instance")

            constructor_name = f"{name}_init_{len(args_ir)}"
            constructor_result = self.env.lookup(constructor_name)
            if constructor_result:
                constructor_func, _ = constructor_result
                final_args = [ptr] + args_ir
                self.builder.call(constructor_func, final_args)
            
            return ptr, ir.PointerType(struct_type)



        print(f">>> CallExpression: calling function '{name}' with {len(params)} arguments")
        
        if name == "print":
            if len(params) == 0:
                return self.report_error("print() requires at least one argument.")

            resolved_args: list[ir.Value] = []
            format_pieces: list[str] = []

            for i, arg_expr in enumerate(params):
                if isinstance(arg_expr, StringLiteral):
                    format_pieces.append(arg_expr.value if arg_expr.value is not None else "")
                    continue

                result = self.resolve_value(arg_expr)
                if result is None:
                    return self.report_error(f"Failed to resolve print argument #{i+1}")
                val, val_type = result

                if isinstance(val_type, ir.PointerType) and isinstance(val_type.pointee, ir.IntType) and val_type.pointee.width == 8: # type: ignore
                    format_pieces.append("%s")
                    resolved_args.append(val)
                    

                elif isinstance(val_type, ir.IntType) and val_type.width == 32:
                    format_pieces.append("%i")
                    resolved_args.append(val)

                elif isinstance(val_type, ir.IntType) and val_type.width == 1:
                    true_ptr = self.builder.gep(
                        self.true_str, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 0)], inbounds=True
                    )
                    false_ptr = self.builder.gep(
                        self.false_str, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 0)], inbounds=True
                    )
                    str_val = self.builder.select(val, true_ptr, false_ptr)
                    format_pieces.append("%s")
                    resolved_args.append(str_val)
                
                elif isinstance(val_type, ir.DoubleType):  
                    format_pieces.append("%lf")
                    resolved_args.append(val)
                    
                elif isinstance(val_type, ir.FloatType):
                    format_pieces.append("%f")   
                    promoted = self.builder.fpext(val, ir.DoubleType())
                    if promoted is not None:
                        resolved_args.append(promoted)
                    else:
                        self.report_error("Failed to promote float to double for print().")
                        return None

                else:
                    return self.report_error(f"Unsupported type for print(): {val_type}")

            
            fmt_string = " ".join(format_pieces) + "\n"
            fmt_global, _ = self.convert_string(fmt_string)
            fmt_ptr = self.builder.gep(
                fmt_global, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 0)], inbounds=True
            )

            print_func_result = self.env.lookup("print")
            if print_func_result is None:
                self.report_error("Built-in function 'print' not found.")
                return None

            return self.builder.call(print_func_result[0], [fmt_ptr, *resolved_args]), self.type_map["int"]


        elif name == "free":
            if len(params) != 1:
                self.report_error("free() requires exactly one pointer argument.")
                return None
            
            
            arg_result = self.resolve_value(params[0])
            if arg_result is None:
                self.report_error("Could not resolve argument for free().")
                return None
            
            ptr_val, ptr_type = arg_result

            i8_ptr_type = ir.IntType(8).as_pointer()
            if ptr_type != i8_ptr_type:
                ptr_val = self.builder.bitcast(ptr_val, i8_ptr_type)

            free_func_result = self.env.lookup("free")
            if free_func_result is None:
                
                self.report_error("Built-in function 'free' not found.")
                return None

            free_func, free_ret_type = free_func_result
            
            ret = self.builder.call(free_func, [ptr_val])
            return ret, free_ret_type 

        
        elif name == "len":
            if len(params) != 1:
                self.report_error("len() requires exactly 1 argument.")
                return None

            arg_resolved = self.resolve_value(params[0])
            if arg_resolved is None:
                return None

            _, arg_type = arg_resolved

            
            if isinstance(arg_type, ir.ArrayType):
                return ir.Constant(self.type_map['int'], arg_type.count), self.type_map['int']

            
            if isinstance(arg_type, ir.PointerType) and isinstance(arg_type.pointee, ir.ArrayType):  # type: ignore
                return ir.Constant(self.type_map['int'], arg_type.pointee.count), self.type_map['int']  # type: ignore

            if isinstance(arg_type, ir.PointerType) and isinstance(arg_type.pointee, ir.IntType): # type: ignore
                if isinstance(params[0], IdentifierLiteral) and params[0].value is not None:
                    arr_name = params[0].value
                    if arr_name in self.array_lengths:
                        return ir.Constant(self.type_map['int'], self.array_lengths[arr_name]), self.type_map['int']
                self.report_error("len() cannot determine size of pointer without stored length.")
                return None

            self.report_error("len() only works on fixed-size arrays.")
            return None
        


        result = self.env.lookup(name)
        if result is None:
            self.report_error(f"Function '{name}' not found in environment.")
            return None
        assert result is not None  
        func, ret_type = result

     
        func = cast(ir.Function, func)
        expected_arg_types: list[ir.Type] = list(func.function_type.args)
        if len(params) != len(expected_arg_types):
            self.report_error(f"Function '{name}' expects {len(expected_arg_types)} arguments, got {len(params)}.")
            return None

        args: list[ir.Value] = []
        for i, arg_expr in enumerate(params):
            result = self.resolve_value(arg_expr)
            if result is None:
                self.report_error(f"Failed to resolve argument #{i + 1} in call to '{name}'")
                return None
            actual_val, actual_type = result
            print(f">>> Arg #{i+1}: value={actual_val}, type={actual_type}")
            expected_type = expected_arg_types[i]

            

            if actual_type != expected_type:
                if isinstance(expected_type, ir.FloatType) and isinstance(actual_type, ir.IntType):
                    actual_val = self.builder.sitofp(actual_val, expected_type)
                elif isinstance(expected_type, ir.IntType) and isinstance(actual_type, ir.FloatType):
                    actual_val = self.builder.fptosi(actual_val, expected_type)

                elif isinstance(expected_type, ir.PointerType) and isinstance(actual_type, ir.PointerType):
                    zero = ir.Constant(ir.IntType(32), 0)

                
                    if isinstance(actual_type.pointee, ir.ArrayType) and isinstance(expected_type.pointee, ir.IntType): # type: ignore
                        actual_val = self.builder.gep(actual_val, [zero, zero], inbounds=True, name=f"arg{i}_array_to_elem")
                        
                    elif isinstance(expected_type.pointee, ir.ArrayType) and isinstance(actual_type.pointee, ir.IntType):# type: ignore
                        actual_val = self.builder.bitcast(actual_val, expected_type)

                    
                    else:
                        actual_val = self.builder.bitcast(actual_val, expected_type)

                else:
                    self.report_error(f"Type mismatch in arg #{i + 1}: cannot cast {actual_type} to {expected_type}")
                    return None

            
            args.append(actual_val)  # type: ignore


        ret: ir.Value = self.builder.call(func, args)
        
        return ret, ret_type


    def visit_reserve_call(self, node: ReserveCall) -> tuple[ir.Value, ir.Type] | None:
        size_result = self.resolve_value(node.size_expr)
        if size_result is None:
            self.report_error("Could not resolve size argument for reserve().")
            return None

        size_val, _ = size_result

        malloc_func_result = self.env.lookup("reserve")
        if malloc_func_result is None:
            self.report_error("Built-in function 'reserve' (malloc) not found.")
            return None
        
        malloc_func, _ = malloc_func_result

        raw_ptr = cast(ir.Value, self.builder.call(malloc_func, [size_val], "malloc_ptr"))
        int_ptr_type: ir.Type = ir.IntType(32).as_pointer()
        cast_ptr = cast(ir.Value, self.builder.bitcast(raw_ptr, int_ptr_type, "int_ptr"))
        return cast_ptr, int_ptr_type


    def visit_prefix_expression(self,node:PrefixExpression)->tuple[ir.Value,ir.Type]|None:
        operator:str=node.operator
        if node.right_node is None:
            self.report_error("Prefic Expression is missing left or right operand.")
            return None

        right_node:Expression=node.right_node

        result=self.resolve_value(right_node)
        if result is None:
            raise SyntaxError("fdxhjbfjd")
        right_value,right_type=result
        Type=None
        value=None
        if operator == '!':
            if not (isinstance(right_type, ir.IntType) and right_type.width == 1):
                self.report_error("Logical NOT operator '!' requires a boolean operand.")
                return None
            # Invert a boolean (i1) by comparing it with false (0).
            value = self.builder.icmp_signed('==', right_value, ir.Constant(ir.IntType(1), 0), name='not_res')
            Type = ir.IntType(1)
        if isinstance(right_type,ir.FloatType):
            Type=ir.FloatType()
            match operator:
                case '-':
                    value=self.builder.fmul(right_value,ir.Constant(ir.FloatType(),-1.0))
        elif isinstance(right_type,ir.IntType):
            Type=ir.IntType(32)
            match operator:
                case '-':
                    value=self.builder.mul(right_value,ir.Constant(ir.IntType(32),-1))

        if value is not None and Type is not None:
            return value, Type

        self.report_error(f"Unsupported operator '{operator}' or incompatible operand types.")
        return None


    def visit_postfix_expression(self, node: PostfixExpression) -> ir.Value | None:
        print(">>> Visiting postfix expression:", type(node.left_node), node.operator)
        if isinstance(node.left_node, IdentifierLiteral):
            print(">>> Postfix on variable:", node.left_node.value)
        if not isinstance(node.left_node, IdentifierLiteral):
            self.report_error("Postfix operator can only be applied to identifiers.")
            return None

        left_node: IdentifierLiteral = node.left_node
        operator: str = node.operator

        if left_node.value is None:
            self.report_error("Identifier in postfix expression has no name.")
            return None

        lookup_result = self.env.lookup(left_node.value)
        if lookup_result is None:
            self.errors.append(f"Compile error: identifier '{left_node.value}' has not been declared.")
            return None

        var_ptr, _ = lookup_result
        orig_value = self.builder.load(var_ptr, name=f"{left_node.value}_val")

        value = None
        match operator:
            case '++':
                if isinstance(orig_value.type, ir.IntType):
                    value = self.builder.add(orig_value, ir.Constant(ir.IntType(32), 1), name=f"{left_node.value}_inc")
                elif isinstance(orig_value.type, ir.FloatType):
                    value = self.builder.fadd(orig_value, ir.Constant(ir.FloatType(), 1.0), name=f"{left_node.value}_finc")
            case '--':
                if isinstance(orig_value.type, ir.IntType):
                    value = self.builder.sub(orig_value, ir.Constant(ir.IntType(32), 1), name=f"{left_node.value}_dec")
                elif isinstance(orig_value.type, ir.FloatType):
                    value = self.builder.fsub(orig_value, ir.Constant(ir.FloatType(), 1.0), name=f"{left_node.value}_fdec")

        if value is not None:
            self.builder.store(value, var_ptr)

  
        return orig_value


    def resolve_value(self, node: Expression, value_type: Optional[str] = None) -> Optional[tuple[ir.Value, ir.Type]]:

        match node.type():
            case NodeType.StructAccessExpression:
                return self.visit_member_access(cast(StructAccessExpression, node))
            case NodeType.MeasureExpression: 
                return self.visit_measure_expression(cast(MeasureExpression, node))
            case NodeType.IntegerLiteral:
                int_node = cast(IntegerLiteral, node)
                value = int_node.value
                Type = self.type_map['int' ]
                return ir.Constant(Type, value), Type

            case NodeType.FloatLiteral:
                float_node = cast(FloatLiteral, node)
                value = float_node.value
                Type = self.type_map['float' ]
                return ir.Constant(Type, value), Type
            
            case NodeType.DoubleLiteral: # Add this case
                double_node = cast(DoubleLiteral, node)
                value = double_node.value
                Type = self.type_map['double']
                return ir.Constant(Type, value), Type

            
            case NodeType.ThisExpression:
                result = self.env.lookup("this")
                if result is None:
                    return self.report_error("'this' can only be used inside a class method.")
                
                return result[0], result[1]
            
            case NodeType.RefExpression:
                return self.visit_ref_expression(cast(RefExpression, node))

            case NodeType.DerefExpression:
                return self.visit_deref_expression(cast(DerefExpression, node))
            case NodeType.ReserveCall:
                return self.visit_reserve_call(cast(ReserveCall, node))
            case NodeType.ArrayLiteral:
                return self.visit_array_literal(cast(ArrayLiteral, node))

            case NodeType.ArrayAccessExpression:
                return self.visit_array_index_expression(cast(ArrayAccessExpression, node))
            
            case NodeType.NullLiteral:
            
                null_ptr_type = ir.IntType(8).as_pointer()
                llvm_null = ir.Constant(null_ptr_type, None)
                return llvm_null, null_ptr_type

            case NodeType.IdentifierLiteral:
                ident_node = cast(IdentifierLiteral, node)
                if ident_node.value is None:
                    raise ValueError("IdentifierLiteral must have a non-null name")

                result = self.env.lookup(ident_node.value)
                if result is None:
                    self.report_error(f"Undefined variable '{ident_node.value}'")
                    return None

                ptr, typ = result

             
                if isinstance(typ, ir.PointerType) and isinstance(typ.pointee, ir.ArrayType):  # type: ignore 
                    zero = ir.Constant(ir.IntType(32), 0)
                    if isinstance(type(ptr), ir.PointerType) and isinstance(type(ptr).pointee, ir.PointerType):  # type: ignore 
                        loaded_array_ptr = self.builder.load(ptr, name=f"{ident_node.value}_arrptr_load")
                        elem_ptr = self.builder.gep(loaded_array_ptr, [zero, zero], inbounds=True, name=f"{ident_node.value}_elem_ptr")
                        return elem_ptr, elem_ptr.type
                    else:
                        elem_ptr = self.builder.gep(ptr, [zero, zero], inbounds=True, name=f"{ident_node.value}_elem_ptr")
                        return elem_ptr, elem_ptr.type

                
                if isinstance(typ, ir.PointerType) and isinstance(typ.pointee, ir.IdentifiedStructType): # type: ignore
            
                    return ptr, typ

                loaded = self.builder.load(ptr, name=f"{ident_node.value}_load")
                return loaded, loaded.type
            
            case NodeType.BooleanLiteral:
                bool_node = cast(BooleanLiteral, node)
                return ir.Constant(ir.IntType(1), 1 if bool_node.value else 0), ir.IntType(1)

            case NodeType.StringLiteral:
                str_node:StringLiteral=cast(StringLiteral, node)
                if str_node.value is None:
                    self.report_error("String literal has no value.")
                    return None
                string,Type=self.convert_string(str_node.value)
                return string,Type

            case NodeType.InfixExpression:
                result = self.visit_infix_expression(cast(InfixExpression, node))
                if result is None:
                    self.report_error("Could not resolve value from infix expression.")
                    return None
                return result
            
            case NodeType.PrefixExpression:
                result = self.visit_prefix_expression(cast(PrefixExpression, node))
                if result is None:
                    self.report_error("Could not resolve value from infix expression.")
                    return None
                return result
            
            case NodeType.PostfixExpression:
                expr = cast(PostfixExpression, node)

                if expr.operator not in ("++", "--"):
                    self.report_error(f"Unsupported postfix operator '{expr.operator}'")
                    return None

                if not isinstance(expr.left_node, IdentifierLiteral):
                    self.report_error("Postfix expressions must target a variable (IdentifierLiteral).")
                    return None

                ident = expr.left_node
                if ident.value is None:
                    self.report_error("PostfixExpression identifier must have a non-null value.")
                    return None
                result = self.env.lookup(ident.value)
                if result is None:
                    self.report_error(f"Variable '{ident.value}' not found.")
                    return None

                ptr, var_type = result
                loaded = self.builder.load(ptr, name=f"{ident.value}_load")

                one = ir.Constant(var_type, 1)
                if expr.operator == "++":
                    updated = self.builder.add(loaded, one, name=f"{ident.value}_inc")
                else:
                    updated = self.builder.sub(loaded, one, name=f"{ident.value}_dec")

                self.builder.store(updated, ptr)
                return loaded, var_type

            case NodeType.InputExpression:
                scanf_func_result = self.env.lookup("input")
                if scanf_func_result is None:
                    self.report_error("Built-in function 'scanf' not found.")
                    return None
                
                scanf_func, _ = scanf_func_result
                if value_type == "int":
                    return self.input_int(scanf_func)
                if value_type == "string":
                    return self.input_string(scanf_func)
                return self.input_string(scanf_func)
                
            case NodeType.CallExpression:
                if isinstance(node, CallExpression):
                    return self.visit_call_expression(node)
                else:
                    self.report_error("Expected CallExpression node, got something else.")
                    return None


    def input_int(self, scanf_func):
        format_string = "%d\0"
        c_fmt = ir.Constant(ir.ArrayType(ir.IntType(8), len(format_string)),
                            bytearray(format_string.encode("utf8")))
        global_fmt = ir.GlobalVariable(self.module, c_fmt.type,
                                    name=f"__scanf_int_format_{self.increment_counter()}")
        global_fmt.linkage = 'internal'
        global_fmt.global_constant = True
        global_fmt.initializer = c_fmt # type: ignore
        fmt_ptr = self.builder.bitcast(global_fmt, ir.IntType(8).as_pointer())

        int_ptr = self.builder.alloca(self.type_map['int'], name="input_val_ptr")
        self.builder.call(scanf_func, [fmt_ptr, int_ptr])
        loaded_value = self.builder.load(int_ptr, name="input_val")
        return loaded_value, self.type_map['int']


    def input_string(self, scanf_func):
        format_string = "%s\0"
        c_fmt = ir.Constant(ir.ArrayType(ir.IntType(8), len(format_string)),
                            bytearray(format_string.encode("utf8")))
        global_fmt = ir.GlobalVariable(self.module, c_fmt.type,
                                    name=f"__scanf_str_format_{self.increment_counter()}")
        global_fmt.linkage = 'internal'
        global_fmt.global_constant = True
        global_fmt.initializer = c_fmt # type: ignore
        fmt_ptr = self.builder.bitcast(global_fmt, ir.IntType(8).as_pointer())

        buf_type = ir.ArrayType(ir.IntType(8), 256) 
        buf = self.builder.alloca(buf_type, name="input_buf")
        str_ptr = self.builder.gep(buf, [ir.Constant(ir.IntType(32), 0),
                                        ir.Constant(ir.IntType(32), 0)],
                                inbounds=True)

        self.builder.call(scanf_func, [fmt_ptr, str_ptr])
        return str_ptr, ir.IntType(8).as_pointer()
                                
                
    def visit_array_literal(self, node: ArrayLiteral) -> tuple[ir.Value, ir.Type] | None:
        if not node.elements:
            self.report_error("Array literals must have at least one element.")
            return None

        element_values = []
        element_types = []

        for element_expr in node.elements:
            result = self.resolve_value(element_expr)
            if result is None:
                self.report_error("Failed to resolve one of the array elements.")
                return None
            val, typ = result
            element_values.append(val)
            element_types.append(typ)

        base_type = element_types[0]
        if not all(t == base_type for t in element_types):
            self.report_error("All array elements must have the same type.")
            return None

        array_len = len(element_values)
        array_type = ir.ArrayType(base_type, array_len)
        array_ptr = self.builder.alloca(array_type, name="array")

        for idx, val in enumerate(element_values):
            element_ptr = self.builder.gep(
                array_ptr,
                [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), idx)],
                inbounds=True
            )
            self.builder.store(val, element_ptr)

        return array_ptr, array_ptr.type

    
    def visit_array_index_expression(self, node: ArrayAccessExpression) -> tuple[ir.Value, ir.Type] | None:
        array_result = self.resolve_value(node.array)
        if array_result is None:
            self.report_error("Failed to resolve array variable in indexing.")
            return None
        array_val, array_type = array_result

        index_result = self.resolve_value(node.index)
        if index_result is None:
            self.report_error("Failed to resolve index in array access.")
            return None
        index_value, index_type = index_result

        if not isinstance(index_type, ir.IntType) or index_type.width != 32:
            self.report_error("Array index must be a 32-bit integer.")
            return None

        if isinstance(array_type, ir.PointerType) and isinstance(array_type.pointee, ir.ArrayType): # type: ignore
            elem_type = array_type.pointee.element  # type: ignore 
            element_ptr = self.builder.gep(
                array_val,
                [ir.Constant(ir.IntType(32), 0), index_value],
                inbounds=True,
                name="array_element_ptr"
            )
        
        elif isinstance(array_type, ir.PointerType) and isinstance(array_type.pointee, ir.IntType): # type: ignore
            elem_type = array_type.pointee  # type: ignore 
            element_ptr = self.builder.gep(
                array_val,
                [index_value],
                inbounds=True,
                name="array_element_ptr"
            )
        else:
            self.report_error("Cannot index into non-array type.")
            return None

        loaded_value = self.builder.load(element_ptr, name="array_element")
        return loaded_value, elem_type


    def convert_string(self,string:str)->tuple[ir.GlobalVariable, ir.Type]:
        string=string.replace("\\n","\n\0")
        fmt:str=f"{string}\0"
        c_fmt:ir.Constant=ir.Constant(ir.ArrayType(ir.IntType(8),len(fmt)),bytearray(fmt.encode("utf8")))

        global_fmt=ir.GlobalVariable(self.module,c_fmt.type,name=f'__str_{self.increment_counter()}')
        global_fmt.linkage='internal'
        global_fmt.global_constant=True
        global_fmt.initializer=c_fmt # type: ignore
        return global_fmt,global_fmt.type
    

    def builtin_printf(self, params: list[ir.Value], return_type: ir.Type) -> ir.Instruction | None:
        func_pair = self.env.lookup("print")
        if func_pair is None:
            self.report_error("Built-in function 'printf' not found.")
            return None
        func, _ = func_pair

        if len(params) == 0:
            self.report_error("printf requires at least one argument (the format string).")
            return None

        format_arg = params[0]
        rest_params = []

    
        if not hasattr(self, "true_str"):
            self.true_str = ir.GlobalVariable(self.module, ir.ArrayType(ir.IntType(8), 5), name="true_str")
            self.true_str.global_constant = True
            self.true_str.initializer = ir.Constant(ir.ArrayType(ir.IntType(8), 5), bytearray(b"true\0")) # type: ignore

            self.false_str = ir.GlobalVariable(self.module, ir.ArrayType(ir.IntType(8), 6), name="false_str")
            self.false_str.global_constant = True
            self.false_str.initializer = ir.Constant(ir.ArrayType(ir.IntType(8), 6), bytearray(b"false\0")) # type: ignore

        def get_string_ptr(global_var):
            zero = ir.Constant(ir.IntType(32), 0)
            return self.builder.gep(global_var, [zero, zero], inbounds=True)

        
        for val in params[1:]:
            val_type = getattr(val, "type", None)
            if isinstance(val_type, ir.IntType) and val_type.width == 1:
                val = self.builder.select(
                    val,
                    get_string_ptr(self.true_str),
                    get_string_ptr(self.false_str),
                )
            rest_params.append(val)

        
        if isinstance(format_arg, ir.LoadInstr):
            g_var_ptr = format_arg.operands[0]
            string_val = self.builder.load(g_var_ptr)
            fmt_arg = self.builder.bitcast(string_val, ir.IntType(8).as_pointer())
        else:
            fmt_arg = self.builder.bitcast(format_arg, ir.IntType(8).as_pointer())

        return self.builder.call(func, [fmt_arg, *rest_params])


    def visit_ref_expression(self, node: RefExpression) -> tuple[ir.Value, ir.Type] | None:
        if not isinstance(node.expression_to_ref, IdentifierLiteral):
            self.report_error("The 'ref' operator can only be applied to a variable.")
            return None

        name = node.expression_to_ref.value
        if name is None:
            self.report_error("Variable name for 'ref' is missing.")
            return None

        entry = self.env.lookup(name)
        if entry is None:
            self.report_error(f"Cannot take reference of undeclared variable '{name}'.")
            return None

        
        ptr, var_type = entry 
        return ptr, ir.PointerType(var_type)


    def visit_deref_expression(self, node: DerefExpression) -> tuple[ir.Value, ir.Type] | None:
        
        pointer_result = self.resolve_value(node.pointer_expression)
        if pointer_result is None:
            self.report_error("Failed to resolve the pointer expression in deref.")
            return None
        
        pointer_val, pointer_type = pointer_result

       
        if not isinstance(pointer_type, ir.PointerType):
            self.report_error("Cannot dereference a non-pointer type.")
            return None

        loaded_value = self.builder.load(pointer_val, name="deref_load")
        
        return loaded_value, pointer_type.pointee # type: ignore
    

    def visit_class_statement(self, node: ClassStatement) -> None:
        class_name = node.name.value
        if class_name is None:
            return self.report_error("Class definition is missing a name.")
        
        if class_name in self.struct_types:
            return self.report_error(f"Class or struct '{class_name}' is already defined.")

        class_type = self.module.context.get_identified_type(class_name)
        self.struct_types[class_name] = class_type
        self.struct_layouts[class_name] = {}
        
        member_types = []
        for i, member_var_stmt in enumerate(node.variables):
            member_name = cast(IdentifierLiteral, member_var_stmt.name).value
            if member_name is None:
                self.report_error(f"Invalid member in class '{class_name}'.")
                continue
            
            
            member_type = self.type_map['int'] 
            member_types.append(member_type)
            self.struct_layouts[class_name][member_name] = i
        
        class_type.set_body(*member_types)

        
        self.class_methods[class_name] = []
        for method_node in node.methods:
            if method_node.name is None or method_node.name.value is None:
                self.report_error("Method in class has no name.")
                continue
            
            
            method_name = method_node.name.value
            
            num_params = len(method_node.parameters) if method_node.parameters else 0
            mangled_name = f"{class_name}_{method_name}_{num_params}"

            method_node.name.value = mangled_name 
            
            self.class_methods[class_name].append(method_name)

            self.compile_method_function(method_node, class_type)
            
            method_node.name.value = method_name 


    def compile_method_function(self, node: FunctionStatement, class_type: ir.IdentifiedStructType) -> None:
        if node.name is None or node.name.value is None:
            raise ValueError("Method name is missing.")
        mangled_name: str = node.name.value

        params: list[FunctionParameter] = node.parameters or []
        param_names: list[str] = [p.name for p in params if p.name]
        param_types: list[ir.Type] = [self.type_map.get(p.value_type if p.value_type is not None else 'int', self.type_map['int']) for p in params]
        
        
        this_param_type = ir.PointerType(class_type)
        final_param_types = [this_param_type] + param_types

       
        return_ir_type = self.type_map.get(node.return_type if node.return_type is not None else 'int', self.type_map['int'])
        
        
        func_type = ir.FunctionType(return_ir_type, final_param_types)
        func = ir.Function(self.module, func_type, name=mangled_name)
        
        self.env.define(mangled_name, func, return_ir_type)


        block = func.append_basic_block(f'{mangled_name}_entry')
        previous_builder = self.builder
        self.builder = ir.IRBuilder(block)

        method_env = Environment(parent=self.env, name=mangled_name)
        previous_env = self.env
        self.env = method_env

        this_ptr = func.args[0]
        self.env.define("this", this_ptr, this_ptr.type)
       
        for i, param_name in enumerate(param_names):
            ptr = self.builder.alloca(param_types[i], name=param_name)
            self.builder.store(func.args[i + 1], ptr) 
            self.env.define(param_name, ptr, param_types[i])

        if node.body:
            self.compile(node.body)

        self.builder = previous_builder
        self.env = previous_env


    def visit_struct_definition_statement(self, node: StructStatement) -> None:
        struct_name = node.name.value
        if struct_name is None:
            self.report_error("Struct definition is missing a name.")
            return
        if struct_name in self.struct_types:
            self.report_error(f"Struct '{struct_name}' is already defined.")
            return

        struct_type = self.module.context.get_identified_type(struct_name)
        
        self.struct_types[struct_name] = struct_type
        
        self.struct_layouts[struct_name] = {}

        member_types = []
        for i, member_var_stmt in enumerate(node.members):
            member_name = cast(IdentifierLiteral, member_var_stmt.name).value
            if member_name is None:
                self.report_error(f"Invalid member in struct '{struct_name}'.")
                continue

            if member_var_stmt.value_type is None:
                member_type = self.type_map['int']
            else:
               
                member_type = self.type_map.get(member_var_stmt.value_type, self.type_map['int'])

            member_types.append(member_type)
            self.struct_layouts[struct_name][member_name] = i
        
        struct_type.set_body(*member_types)


    def visit_struct_instantiation(self, node: StructInstanceExpression) -> Optional[tuple[ir.Value, ir.Type]]:
        
        struct_name = node.struct_name.value
        if struct_name is None:
            self.report_error("Struct instantiation is missing a name.")
            return None

        struct_type = self.struct_types.get(struct_name)
        if struct_type is None:
            self.report_error(f"Attempting to instantiate unknown struct type '{struct_name}'.")
            return None

        
        ptr = self.builder.alloca(struct_type, name=f"{struct_name}_instance")
        
        return ptr, ir.PointerType(struct_type)


    def visit_member_access(self, node: StructAccessExpression) -> Optional[tuple[ir.Value, ir.Type]]:
        member_name = node.member_name.value
        if member_name is None:
            self.report_error("Member access is missing a member name.")
            return None

        obj_resolved = self.resolve_value(node.struct_name)
        if obj_resolved is None:
            self.report_error("Could not resolve object in member access.")
            return None
        obj_ptr, obj_type = obj_resolved

        if not isinstance(obj_type, ir.PointerType) or not isinstance(obj_type.pointee, ir.IdentifiedStructType): # type: ignore
            self.report_error("Member access '.' operator can only be used on struct instances.")
            return None

        struct_type = cast(ir.IdentifiedStructType, obj_type.pointee) # type: ignore
        struct_name = struct_type.name
        layout = self.struct_layouts.get(struct_name)
        member_index = layout.get(member_name) if layout else None

        if member_index is None:
            self.report_error(f"Struct '{struct_name}' has no member named '{member_name}'.")
            return None

        zero = ir.Constant(ir.IntType(32), 0)
        member_ptr = self.builder.gep(obj_ptr, [zero, ir.Constant(ir.IntType(32), member_index)], inbounds=True, name=f"{member_name}_ptr")

        loaded_value = self.builder.load(member_ptr, name=member_name)
        return loaded_value, loaded_value.type 
