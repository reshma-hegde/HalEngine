import cmath
import math
import random
from llvmlite import ir
import os
from AST import DoubleLiteral, Node,NodeType,Program, RaiseStatement,Statement,Expression, VarStatement,IdentifierLiteral,ReturnStatement,AssignStatement,CallExpression,InputExpression,NullLiteral, ClassStatement,ThisExpression,BranchStatement,ForkStatement,QubitDeclarationStatement,MeasureExpression
from AST import ExpressionStatement,InfixExpression,IntegerLiteral,FloatLiteral, BlockStatement,FunctionStatement,IfStatement,BooleanLiteral,ArrayLiteral,RefExpression,DerefExpression,ReserveCall,RewindStatement, FastForwardStatement,SuperExpression,AsExpression
from AST import FunctionParameter,StringLiteral,WhileStatement,BreakStatement,ContinueStatement,PrefixExpression,PostfixExpression,LoadStatement,ArrayAccessExpression, StructInstanceExpression,StructAccessExpression,StructStatement,QubitResetStatement,CastExpression
from typing import List, cast
from Environment import Environment
from typing import Optional
from lexer import Lexer
from Parser import Parser

BUILTIN_HEADERS = {
    
}


class Compiler:
    def __init__(self)-> None:
        self.module:ir.Module=ir.Module('main')
        self.errors: list[str] = []
        self.array_lengths: dict[str, int] = {}
        self.struct_types: dict[str, ir.IdentifiedStructType] = {}
        self.struct_layouts: dict[str, dict[str, int]] = {}
        self.class_methods: dict[str, list[str]] = {}
        self.class_parents: dict[str, str] = {}
        self.type_map:dict[str,ir.Type]={
            'int':ir.IntType(32),
            'float':ir.FloatType(),
            'double':ir.DoubleType(),
            'void':ir.VoidType(),
            'bool':ir.IntType(1),
            'str':ir.PointerType(ir.IntType(8)),
            'file': ir.PointerType(ir.IntType(8)),
            'null': ir.VoidType(),
            'qubit':ir.IntType(32)
        }
        
        complex_type = self.module.context.get_identified_type("complex")
        complex_type.set_body(ir.DoubleType(), ir.DoubleType()) 
        self.struct_types["complex"] = complex_type
        self.struct_layouts["complex"] = {"real": 0, "imag": 1}


        vector_type = self.module.context.get_identified_type("vector")
        vector_type.set_body(
            ir.PointerType(ir.DoubleType()),
            ir.IntType(32)
        )
        self.struct_types["vector"] = vector_type
        self.struct_layouts["vector"] = {"data": 0, "size": 1}

        self.counter:int=0
        self.generic_functions: dict[str, FunctionStatement] = {}

        self.exception_handler_stack: list[ir.Block] = []
        self.global_error_ptr: Optional[ir.GlobalVariable] = None
        
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

        def __init_fopen()->ir.Function:
            
            fnty:ir.FunctionType=ir.FunctionType(
                self.type_map['file'],
                [ir.IntType(8).as_pointer(), ir.IntType(8).as_pointer()],
                var_arg=False
            )
            return ir.Function(self.module,fnty,'fopen')

        def __init_fclose()->ir.Function:
            
            fnty:ir.FunctionType=ir.FunctionType(
                self.type_map['int'],
                [self.type_map['file']],
                var_arg=False
            )
            return ir.Function(self.module,fnty,'fclose')

        def __init_fputs()->ir.Function:
            
            fnty:ir.FunctionType=ir.FunctionType(
                self.type_map['int'],
                [ir.IntType(8).as_pointer(), self.type_map['file']],
                var_arg=False
            )
            return ir.Function(self.module,fnty,'fputs')

        def __init_fgets()->ir.Function:
            
            fnty:ir.FunctionType=ir.FunctionType(
                ir.IntType(8).as_pointer(),
                [ir.IntType(8).as_pointer(), self.type_map['int'], self.type_map['file']],
                var_arg=False
            )
            return ir.Function(self.module, fnty, 'fgets')
        
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
            null_type = self.type_map['int'].as_pointer() 
            null_var = ir.GlobalVariable(self.module, null_type, 'null')
            null_var.initializer = ir.Constant(null_type, None) # type: ignore
            null_var.global_constant = True
            return null_var
        
        def __init_realloc()->ir.Function:
            fnty:ir.FunctionType=ir.FunctionType(
                ir.IntType(8).as_pointer(), 
                [ir.IntType(8).as_pointer(), ir.IntType(32)], 
                var_arg=False
            )
            return ir.Function(self.module,fnty,'realloc')     

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

        self.env.define('open', __init_fopen(), self.type_map['file'])
        self.env.define('close', __init_fclose(), self.type_map['int'])
        self.env.define('write', __init_fputs(), self.type_map['int'])
        self.env.define('read_line', __init_fgets(), ir.IntType(8).as_pointer())
                
        #print
        self.env.define('print',__init_print(),ir.IntType(32))
        self.env.define('input',__init_scanf(),ir.IntType(32))
        self.env.define('reserve', __init_malloc(), ir.IntType(8).as_pointer())
        self.env.define('realloc', __init_realloc(), ir.IntType(8).as_pointer())
        self.env.define('free', __init_free(), ir.VoidType())
        true_var,false_var=__init_booleans()
        self.env.define('true',true_var,true_var.type)
        self.env.define('false',false_var,false_var.type)

        null_var = __init_null()
        self.env.define('null', null_var, null_var.type)
        self.__initialize_math_builtins()
        error_val_type = ir.IntType(8).as_pointer()
        self.global_error_ptr = ir.GlobalVariable(self.module, error_val_type, name="__global_error_val")
        self.global_error_ptr.initializer = ir.Constant(error_val_type, None) # type: ignore
        self.global_error_ptr.linkage = 'internal'

        self.__define_print_vector_helper()


    
    def __initialize_math_builtins(self) -> None:
        double_type = ir.DoubleType()
        fnty = ir.FunctionType(double_type, [double_type])
        sin_func = ir.Function(self.module, fnty, 'sin')
        self.env.define('sin', sin_func, double_type)

        cos_func = ir.Function(self.module, fnty, 'cos')
        self.env.define('cos', cos_func, double_type)

        tan_func = ir.Function(self.module, fnty, 'tan')
        self.env.define('tan', tan_func, double_type)

        self.env.define('cot', ir.Function(self.module, fnty, 'cot'), double_type)
        self.env.define('sec', ir.Function(self.module, fnty, 'sec'), double_type)
        self.env.define('cosec', ir.Function(self.module, fnty, 'cosec'), double_type)

        sqrt_func = ir.Function(self.module, ir.FunctionType(double_type, [double_type]), 'sqrt')
        self.env.define('sqrt', sqrt_func, double_type)
        

    def increment_counter(self)->int:
        self.counter+=1
        return self.counter


    def compile(self, node: Node) -> None:
        match node.type():
            case NodeType.Program:
                self.visit_program(cast(Program, node))
            case NodeType.BranchStatement:
                self.visit_branch_statement(cast(BranchStatement, node))   
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
            case NodeType.RaiseStatement:
                self.visit_raise_statement(cast(RaiseStatement, node))   
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

    def _get_global_env(self) -> Environment:
        env = self.env
        while env.parent:
            env = env.parent
        return env    

    def visit_program(self, node: Program) -> None:
        for stmt in node.statements:
            t = stmt.type()
            if t in (NodeType.ClassStatement, NodeType.StructStatement):
                self.compile(stmt)

        concrete_statements = []
        for stmt in node.statements:
            
            if stmt.type() in (NodeType.ClassStatement, NodeType.StructStatement):
                continue
            
            is_generic = False
            if isinstance(stmt, FunctionStatement):
                if stmt.parameters:
                    for param in stmt.parameters:
                        if param.value_type == 'var':
                            is_generic = True
                            break
            
            if is_generic and isinstance(stmt, FunctionStatement) and stmt.name and stmt.name.value:
                self.generic_functions[stmt.name.value] = stmt
            else:
                concrete_statements.append(stmt)
        
        for stmt in concrete_statements:
            self.compile(stmt)


    def visit_branch_statement(self, node: BranchStatement) -> None:
       
        current_func = self.builder.function

        handle_block = current_func.append_basic_block("handle_block")
        merge_block = current_func.append_basic_block("merge_block")
        self.exception_handler_stack.append(handle_block)

        self.compile(node.try_block)
        
        if self.builder.block is not None:
            block = self.builder.block
            if not block.is_terminated:
                self.builder.branch(merge_block)

        self.builder.position_at_start(handle_block)

        self.exception_handler_stack.pop()

        if self.global_error_ptr is not None:
            error_val = self.builder.load(self.global_error_ptr, "error_val")
            error_var_name = node.error_variable.value

            if error_var_name:
                err_var_ptr = self.builder.alloca(error_val.type, name=error_var_name)
                self.builder.store(error_val, err_var_ptr)
                self.env.define(error_var_name, err_var_ptr, error_val.type)

            null_ptr = ir.Constant(self.global_error_ptr.type.pointee, None) # type: ignore
            self.builder.store(null_ptr, self.global_error_ptr)

        self.compile(node.handle_block)
      
        if self.builder.block is not None:
            block = self.builder.block
            if not block.is_terminated:
                self.builder.branch(merge_block)

        self.builder.position_at_start(merge_block)

   
    def visit_raise_statement(self, node: "RaiseStatement") -> None:
        if not self.exception_handler_stack:
            self.report_error("'raise' statement used outside of a 'branch...handle' block. Program will terminate.")
            return

        error_val_resolved = self.resolve_value(node.value)
        if error_val_resolved is None:
            self.report_error("Could not resolve value for 'raise' statement.")
            return
        error_val, error_type = error_val_resolved

        if self.global_error_ptr is not None:
            target_type = self.global_error_ptr.type.pointee # type: ignore
            
            if error_type != target_type:
                self.report_error(f"Cannot raise value of type {error_type}. Only strings are supported.")
                return

            self.builder.store(error_val, self.global_error_ptr)
        
        handler_block = self.exception_handler_stack[-1]
        self.builder.branch(handler_block)

    
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
        outcome_types: List[ir.Type] = []

        for branch in node.branches:
            
            self.builder.store(initial_value, var_ptr)
           
            self.compile(branch)
            
            final_value = self.builder.load(var_ptr, name=f"{target_var_name}_outcome")
            outcome_values.append(final_value)
            outcome_types.append(final_value.type)

        
        if not outcome_values:
            return

        merge_var_name = node.merge_variable.value
        if merge_var_name is None:
            self.report_error("Merge statement is missing a result variable name.")
            return

        num_outcomes = len(outcome_values)
       
        outcome_element_type = outcome_types[0]
        is_numeric = all(isinstance(t, (ir.IntType, ir.FloatType, ir.DoubleType)) for t in outcome_types)
        if is_numeric:
            if any(isinstance(t, ir.DoubleType) for t in outcome_types):
                outcome_element_type = self.type_map['double']
            elif any(isinstance(t, ir.FloatType) for t in outcome_types):
                outcome_element_type = self.type_map['float']
        
        array_type = ir.ArrayType(outcome_element_type, num_outcomes)
        result_array_ptr = self.builder.alloca(array_type, name=merge_var_name)

        for i, value in enumerate(outcome_values):
            
            promoted_value = value
            value_type = getattr(value, "type", None)
            if value_type != outcome_element_type:
                if isinstance(outcome_element_type, (ir.FloatType, ir.DoubleType)) and isinstance(value_type, ir.IntType):
                    promoted_value = self.builder.sitofp(value, outcome_element_type)
                
            idx = ir.Constant(ir.IntType(32), i)
            element_ptr = self.builder.gep(result_array_ptr, [ir.Constant(ir.IntType(32), 0), idx], inbounds=True)
            self.builder.store(promoted_value, element_ptr)

        self.env.define(merge_var_name, result_array_ptr, result_array_ptr.type)
        if merge_var_name:
             self.array_lengths[merge_var_name] = num_outcomes
              
        

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
            ir_type.pointee, ir.ArrayType   # type: ignore
        ):
            
            self.array_lengths[name] = ir_type.pointee.count # type: ignore

            self.env.define(name, value_ir, ir_type)
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
            return

        value, typ = resolved

        current_function = self.builder.function
        expected_return_type = current_function.return_value.type

        if typ != expected_return_type:
            if isinstance(typ, ir.PointerType) and isinstance(expected_return_type, ir.PointerType):
                value = self.builder.bitcast(value, expected_return_type, name="return_cast")
            
        self.builder.ret(value)

    def _find_and_infer_return_type(self, node: Node) -> Optional[ir.Type]:
        
        if isinstance(node, BlockStatement):
            for stmt in node.statements:
                result = self._find_and_infer_return_type(stmt)
                if result:
                    return result
        elif isinstance(node, IfStatement):
            if node.consequence:
                result = self._find_and_infer_return_type(node.consequence)
                if result:
                    return result
            if node.el_if:
                result = self._find_and_infer_return_type(node.el_if)
                if result:
                    return result
            if node.alternative:
                result = self._find_and_infer_return_type(node.alternative)
                if result:
                    return result
        elif isinstance(node, ReturnStatement) and node.return_value is not None:
            
            resolved = self.resolve_value(node.return_value)
            if resolved:
                _, ir_type = resolved
                return ir_type
        return None

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

        
        global_env=self._get_global_env()
        previous_builder = self.builder
        previous_env = self.env
        dummy_module = ir.Module(name=f"{name}_dummy_module")
        dummy_func = ir.Function(dummy_module, ir.FunctionType(ir.VoidType(), param_types), name=f"{name}_dummy_temp")
        dummy_block = dummy_func.append_basic_block("entry")
        
        self.builder = ir.IRBuilder(dummy_block)
        self.env = Environment(parent=global_env)
        self.env.define(name, dummy_func, ir.VoidType()) 
        
        for i, param_name in enumerate(param_names):
            dummy_ptr = self.builder.alloca(param_types[i])
            self.env.define(param_name, dummy_ptr, param_types[i])

        self.compile(body)
        
        
        actual_inferred_ir_type = self._find_and_infer_return_type(body)
        
        if node.return_type is None:
            inferred_type: str | None = None
            if actual_inferred_ir_type:
                if isinstance(actual_inferred_ir_type, ir.IntType) and actual_inferred_ir_type.width == 1: inferred_type = "bool"
                elif isinstance(actual_inferred_ir_type, ir.IntType): inferred_type = "int"
                elif isinstance(actual_inferred_ir_type, ir.FloatType): inferred_type = "float"
                elif isinstance(actual_inferred_ir_type, ir.DoubleType): inferred_type = "double"
                elif isinstance(actual_inferred_ir_type, ir.PointerType):
                    pointee = actual_inferred_ir_type.pointee# type: ignore
                    if isinstance(pointee, ir.IntType) and pointee.width == 8:
                        inferred_type = "str"
                    else:
                        inferred_type = "array"
            
            ret_type_str = inferred_type if inferred_type is not None else "void"
        else:
            ret_type_str = node.return_type

        node.return_type = ret_type_str
        self.builder = previous_builder
        self.env = previous_env

        
        if ret_type_str == "array" and actual_inferred_ir_type is not None:
            return_ir_type = actual_inferred_ir_type
        else:
            return_ir_type = self.type_map.get(ret_type_str, ir.VoidType())
    
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

        for i, param_name in enumerate(param_names):
            if isinstance(param_types[i], ir.PointerType) and isinstance(param_types[i].pointee, ir.ArrayType): # type: ignore
                self.env.define(param_name, func.args[i], param_types[i])
            else:
                ptr = self.builder.alloca(param_types[i], name=param_name)
                self.builder.store(func.args[i], ptr)
                self.env.define(param_name, ptr, param_types[i])
        
        self.compile(body)

        if self.builder.block is not None and not self.builder.block.is_terminated:
            if ret_type_str == "void":
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
                
                this_entry = self.env.lookup("this")
                if this_entry:
                    this_ptr, this_type = this_entry
                    class_type = this_type.pointee # type: ignore
                    class_name = class_type.name
                    layout = self.struct_layouts.get(class_name)
                    
                    if layout and name in layout:
                        member_index = layout[name]
                        zero = ir.Constant(ir.IntType(32), 0)
                        idx = ir.Constant(ir.IntType(32), member_index)
                        
                        if node.operator == '=':
                            member_ptr = self.builder.gep(this_ptr, [zero, idx], inbounds=True, name=f"{name}_ptr")
                            self.builder.store(right_value, member_ptr)
                            return 
                        else:
                            self.errors.append(f"COMPILE ERROR: Compound assignment ('{node.operator}') on class members is not yet supported.")
                            return

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

        
        if node.alternative is None and node.el_if is None:
            with self.builder.if_then(test):
                if node.consequence is not None:
                    self.compile(node.consequence)
        else:
       
            with self.builder.if_else(test) as (then_block, else_block):
                with then_block:
                    if node.consequence is not None:
                        self.compile(node.consequence)
                
                with else_block:
                    if node.el_if is not None:
                        self.compile(node.el_if)
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

        is_left_hypocrisy = (isinstance(left_type, ir.PointerType) and
                             isinstance(left_type.pointee, ir.IdentifiedStructType) and # type: ignore
                             left_type.pointee.name.startswith("hypocrisy_")) # type: ignore

        is_right_hypocrisy = (isinstance(right_type, ir.PointerType) and
                              isinstance(right_type.pointee, ir.IdentifiedStructType) and # type: ignore
                              right_type.pointee.name.startswith("hypocrisy_")) # type: ignore

        if is_left_hypocrisy and is_right_hypocrisy:
            if left_type != right_type:
                self.report_error(f"Cannot perform '{operator}' on hypocrisy variables of different underlying types.")
                return None

            left_seen_ptr = self.builder.gep(left_value, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 0)], inbounds=True)
            left_truth_ptr = self.builder.gep(left_value, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 1)], inbounds=True)
            left_seen = self.builder.load(left_seen_ptr, "left_seen")
            left_truth = self.builder.load(left_truth_ptr, "left_truth")

            right_seen_ptr = self.builder.gep(right_value, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 0)], inbounds=True)
            right_truth_ptr = self.builder.gep(right_value, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 1)], inbounds=True)
            right_seen = self.builder.load(right_seen_ptr, "right_seen")
            right_truth = self.builder.load(right_truth_ptr, "right_truth")
            
            is_float_op = isinstance(left_seen.type, (ir.FloatType, ir.DoubleType))
            
            result_seen, result_truth = None, None

            op_map = {
                '+': (self.builder.fadd, self.builder.add),
                '-': (self.builder.fsub, self.builder.sub),
                '*': (self.builder.fmul, self.builder.mul),
                '/': (self.builder.fdiv, self.builder.sdiv)
            }

            if operator not in op_map:
                self.report_error(f"Operator '{operator}' is not supported for hypocrisy variables.")
                return None
            
            f_op, i_op = op_map[operator]
            op_func = f_op if is_float_op else i_op
            
            result_seen = op_func(left_seen, right_seen, "seen_res")
            result_truth = op_func(left_truth, right_truth, "truth_res")

            result_struct_type = left_type.pointee # type: ignore
            result_ptr = self.builder.alloca(result_struct_type, name="hypocrisy_res")

            self.builder.store(result_seen, self.builder.gep(result_ptr, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 0)]))
            self.builder.store(result_truth, self.builder.gep(result_ptr, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 1)]))

            return result_ptr, left_type

        vector_struct_type = self.struct_types.get("vector")
        is_left_vec = isinstance(left_type, ir.PointerType) and left_type.pointee == vector_struct_type # type: ignore
        is_right_vec = isinstance(right_type, ir.PointerType) and right_type.pointee == vector_struct_type # type: ignore
        is_left_num = isinstance(left_type, (ir.IntType, ir.FloatType, ir.DoubleType))
        is_right_num = isinstance(right_type, (ir.IntType, ir.FloatType, ir.DoubleType))

        if is_left_vec and is_right_vec and operator in ('+', '-'):
            size_ptr = self.builder.gep(left_value, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 1)], inbounds=True)
            size = self.builder.load(size_ptr)
            
            lookup_resul = self.env.lookup("reserve")
            if lookup_resul is None:
                return self.report_error("Builtin 'reserve' not found in environment.")

            malloc_func = lookup_resul[0]
            double_size = ir.Constant(ir.IntType(32), 8)
            alloc_size = self.builder.mul(size, double_size)
            new_data_ptr = self.builder.call(malloc_func, [alloc_size])
            new_data_ptr = self.builder.bitcast(new_data_ptr, ir.PointerType(ir.DoubleType()))
            
            result_vec_ptr = self.builder.alloca(vector_struct_type, name="vec_result")
            result_data_field_ptr = self.builder.gep(result_vec_ptr, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 0)], inbounds=True)
            result_size_field_ptr = self.builder.gep(result_vec_ptr, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 1)], inbounds=True)
            self.builder.store(new_data_ptr, result_data_field_ptr)
            self.builder.store(size, result_size_field_ptr)

            left_data_ptr = self.builder.load(self.builder.gep(left_value, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 0)], inbounds=True))
            right_data_ptr = self.builder.load(self.builder.gep(right_value, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 0)], inbounds=True))

            loop_cond = self.builder.append_basic_block('loop_cond_vec_op')
            loop_body = self.builder.append_basic_block('loop_body_vec_op')
            loop_exit = self.builder.append_basic_block('loop_exit_vec_op')
            
            counter_ptr = self.builder.alloca(ir.IntType(32), name='i')
            self.builder.store(ir.Constant(ir.IntType(32), 0), counter_ptr)
            self.builder.branch(loop_cond)

            self.builder.position_at_start(loop_cond)
            i = self.builder.load(counter_ptr)
            cond = self.builder.icmp_signed('<', i, size)
            self.builder.cbranch(cond, loop_body, loop_exit)

            self.builder.position_at_start(loop_body)
            left_elem = self.builder.load(self.builder.gep(left_data_ptr, [i], inbounds=True))
            right_elem = self.builder.load(self.builder.gep(right_data_ptr, [i], inbounds=True))
            
            if operator == '+':
                result_elem = self.builder.fadd(left_elem, right_elem)
            else: 
                result_elem = self.builder.fsub(left_elem, right_elem)
            
            self.builder.store(result_elem, self.builder.gep(new_data_ptr, [i], inbounds=True))
            
            next_i = self.builder.add(i, ir.Constant(ir.IntType(32), 1))
            self.builder.store(next_i, counter_ptr)
            self.builder.branch(loop_cond)

            self.builder.position_at_start(loop_exit)
            return result_vec_ptr, left_type

        if (is_left_vec and is_right_num) or (is_right_vec and is_left_num) and operator == '*':
            vec_val = left_value if is_left_vec else right_value
            scalar_val = right_value if is_left_vec else left_value
            scalar_type = right_type if is_left_vec else left_type

            if not isinstance(scalar_type, ir.DoubleType):
                if isinstance(scalar_type, ir.IntType):
                    scalar_val = self.builder.sitofp(scalar_val, ir.DoubleType())
                else: 
                    scalar_val = self.builder.fpext(scalar_val, ir.DoubleType())

            size_ptr = self.builder.gep(vec_val, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 1)], inbounds=True)
            size = self.builder.load(size_ptr)
            lookup_resul = self.env.lookup("reserve")
            if lookup_resul is None:
                return self.report_error("Builtin 'reserve' not found in environment.")

            malloc_func = lookup_resul[0]

            alloc_size = self.builder.mul(size, ir.Constant(ir.IntType(32), 8))
            new_data_ptr = self.builder.call(malloc_func, [alloc_size])
            new_data_ptr = self.builder.bitcast(new_data_ptr, ir.PointerType(ir.DoubleType()))
            
            result_vec_ptr = self.builder.alloca(vector_struct_type, name="vec_scalar_result")
            self.builder.store(new_data_ptr, self.builder.gep(result_vec_ptr, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 0)], inbounds=True))
            self.builder.store(size, self.builder.gep(result_vec_ptr, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 1)], inbounds=True))
            
            vec_data_ptr = self.builder.load(self.builder.gep(vec_val, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 0)], inbounds=True))

            loop_cond_s = self.builder.append_basic_block('loop_cond_vec_s')
            loop_body_s = self.builder.append_basic_block('loop_body_vec_s')
            loop_exit_s = self.builder.append_basic_block('loop_exit_vec_s')
            counter_ptr_s = self.builder.alloca(ir.IntType(32), name='i_s')
            self.builder.store(ir.Constant(ir.IntType(32), 0), counter_ptr_s)
            self.builder.branch(loop_cond_s)
            self.builder.position_at_start(loop_cond_s)
            i_s = self.builder.load(counter_ptr_s)
            cond_s = self.builder.icmp_signed('<', i_s, size)
            self.builder.cbranch(cond_s, loop_body_s, loop_exit_s)
            self.builder.position_at_start(loop_body_s)
            elem = self.builder.load(self.builder.gep(vec_data_ptr, [i_s], inbounds=True))
            result_elem = self.builder.fmul(elem, scalar_val)
            self.builder.store(result_elem, self.builder.gep(new_data_ptr, [i_s], inbounds=True))
            next_i_s = self.builder.add(i_s, ir.Constant(ir.IntType(32), 1))
            self.builder.store(next_i_s, counter_ptr_s)
            self.builder.branch(loop_cond_s)
            self.builder.position_at_start(loop_exit_s)

            return result_vec_ptr, ir.PointerType(vector_struct_type)


        is_left_complex = isinstance(left_type, ir.PointerType) and isinstance(left_type.pointee, ir.IdentifiedStructType) and left_type.pointee.name == "complex" # type: ignore
        is_right_complex = isinstance(right_type, ir.PointerType) and isinstance(right_type.pointee, ir.IdentifiedStructType) and right_type.pointee.name == "complex" # type: ignore

        if is_left_complex and is_right_complex and operator == '+':
        
            left_real_ptr = self.builder.gep(left_value, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 0)], inbounds=True)
            left_imag_ptr = self.builder.gep(left_value, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 1)], inbounds=True)
            left_real = self.builder.load(left_real_ptr)
            left_imag = self.builder.load(left_imag_ptr)

            
            right_real_ptr = self.builder.gep(right_value, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 0)], inbounds=True)
            right_imag_ptr = self.builder.gep(right_value, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 1)], inbounds=True)
            right_real = self.builder.load(right_real_ptr)
            right_imag = self.builder.load(right_imag_ptr)

            
            res_real = self.builder.fadd(left_real, right_real, "res_real")
            res_imag = self.builder.fadd(left_imag, right_imag, "res_imag")

            complex_type = self.struct_types["complex"]
            
            res_ptr = self.builder.alloca(complex_type, name="complex_add_res")
            
            res_real_ptr = self.builder.gep(res_ptr, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 0)], inbounds=True)
            res_imag_ptr = self.builder.gep(res_ptr, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 1)], inbounds=True)
            self.builder.store(res_real, res_real_ptr)
            self.builder.store(res_imag, res_imag_ptr)

            return res_ptr, ir.PointerType(complex_type)
        
        if is_left_complex and is_right_complex and operator == '-':
            left_real_ptr = self.builder.gep(left_value, [ir.Constant(ir.IntType(32), 0),
                                                        ir.Constant(ir.IntType(32), 0)], inbounds=True)
            left_imag_ptr = self.builder.gep(left_value, [ir.Constant(ir.IntType(32), 0),
                                                        ir.Constant(ir.IntType(32), 1)], inbounds=True)
            left_real = self.builder.load(left_real_ptr)
            left_imag = self.builder.load(left_imag_ptr)

            right_real_ptr = self.builder.gep(right_value, [ir.Constant(ir.IntType(32), 0),
                                                            ir.Constant(ir.IntType(32), 0)], inbounds=True)
            right_imag_ptr = self.builder.gep(right_value, [ir.Constant(ir.IntType(32), 0),
                                                            ir.Constant(ir.IntType(32), 1)], inbounds=True)
            right_real = self.builder.load(right_real_ptr)
            right_imag = self.builder.load(right_imag_ptr)

            res_real = self.builder.fsub(left_real, right_real, "res_real")
            res_imag = self.builder.fsub(left_imag, right_imag, "res_imag")

            complex_type = self.struct_types["complex"]
            res_ptr = self.builder.alloca(complex_type, name="complex_sub_res")

            res_real_ptr = self.builder.gep(res_ptr, [ir.Constant(ir.IntType(32), 0),
                                                    ir.Constant(ir.IntType(32), 0)], inbounds=True)
            res_imag_ptr = self.builder.gep(res_ptr, [ir.Constant(ir.IntType(32), 0),
                                                    ir.Constant(ir.IntType(32), 1)], inbounds=True)
            self.builder.store(res_real, res_real_ptr)
            self.builder.store(res_imag, res_imag_ptr)

            return res_ptr, ir.PointerType(complex_type)
        
        if is_left_complex and is_right_complex and operator == '*':
            left_real_ptr = self.builder.gep(left_value, [ir.Constant(ir.IntType(32), 0),
                                                        ir.Constant(ir.IntType(32), 0)], inbounds=True)
            left_imag_ptr = self.builder.gep(left_value, [ir.Constant(ir.IntType(32), 0),
                                                        ir.Constant(ir.IntType(32), 1)], inbounds=True)
            left_real = self.builder.load(left_real_ptr)
            left_imag = self.builder.load(left_imag_ptr)

            right_real_ptr = self.builder.gep(right_value, [ir.Constant(ir.IntType(32), 0),
                                                            ir.Constant(ir.IntType(32), 0)], inbounds=True)
            right_imag_ptr = self.builder.gep(right_value, [ir.Constant(ir.IntType(32), 0),
                                                            ir.Constant(ir.IntType(32), 1)], inbounds=True)
            right_real = self.builder.load(right_real_ptr)
            right_imag = self.builder.load(right_imag_ptr)

            ac = self.builder.fmul(left_real, right_real, "ac")
            bd = self.builder.fmul(left_imag, right_imag, "bd")
            ad = self.builder.fmul(left_real, right_imag, "ad")
            bc = self.builder.fmul(left_imag, right_real, "bc")

            res_real = self.builder.fsub(ac, bd, "res_real")
            res_imag = self.builder.fadd(ad, bc, "res_imag")

            complex_type = self.struct_types["complex"]
            res_ptr = self.builder.alloca(complex_type, name="complex_mul_res")

            res_real_ptr = self.builder.gep(res_ptr, [ir.Constant(ir.IntType(32), 0),
                                                    ir.Constant(ir.IntType(32), 0)], inbounds=True)
            res_imag_ptr = self.builder.gep(res_ptr, [ir.Constant(ir.IntType(32), 0),
                                                    ir.Constant(ir.IntType(32), 1)], inbounds=True)
            self.builder.store(res_real, res_real_ptr)
            self.builder.store(res_imag, res_imag_ptr)

            return res_ptr, ir.PointerType(complex_type)
        
        if is_left_complex and is_right_complex and operator == '/':
            left_real_ptr = self.builder.gep(left_value, [ir.Constant(ir.IntType(32), 0),
                                                        ir.Constant(ir.IntType(32), 0)], inbounds=True)
            left_imag_ptr = self.builder.gep(left_value, [ir.Constant(ir.IntType(32), 0),
                                                        ir.Constant(ir.IntType(32), 1)], inbounds=True)
            left_real = self.builder.load(left_real_ptr)
            left_imag = self.builder.load(left_imag_ptr)

            right_real_ptr = self.builder.gep(right_value, [ir.Constant(ir.IntType(32), 0),
                                                            ir.Constant(ir.IntType(32), 0)], inbounds=True)
            right_imag_ptr = self.builder.gep(right_value, [ir.Constant(ir.IntType(32), 0),
                                                            ir.Constant(ir.IntType(32), 1)], inbounds=True)
            right_real = self.builder.load(right_real_ptr)
            right_imag = self.builder.load(right_imag_ptr)

            c2 = self.builder.fmul(right_real, right_real, "c2")
            d2 = self.builder.fmul(right_imag, right_imag, "d2")
            denom = self.builder.fadd(c2, d2, "denom")

            ac = self.builder.fmul(left_real, right_real, "ac")
            bd = self.builder.fmul(left_imag, right_imag, "bd")
            num_real = self.builder.fadd(ac, bd, "num_real")

            bc = self.builder.fmul(left_imag, right_real, "bc")
            ad = self.builder.fmul(left_real, right_imag, "ad")
            num_imag = self.builder.fsub(bc, ad, "num_imag")

            res_real = self.builder.fdiv(num_real, denom, "res_real")
            res_imag = self.builder.fdiv(num_imag, denom, "res_imag")

            complex_type = self.struct_types["complex"]
            res_ptr = self.builder.alloca(complex_type, name="complex_div_res")

            res_real_ptr = self.builder.gep(res_ptr, [ir.Constant(ir.IntType(32), 0),
                                                    ir.Constant(ir.IntType(32), 0)], inbounds=True)
            res_imag_ptr = self.builder.gep(res_ptr, [ir.Constant(ir.IntType(32), 0),
                                                    ir.Constant(ir.IntType(32), 1)], inbounds=True)
            self.builder.store(res_real, res_real_ptr)
            self.builder.store(res_imag, res_imag_ptr)

            return res_ptr, ir.PointerType(complex_type)



        
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
            if isinstance(left_type, ir.PointerType) and isinstance(right_type, ir.IntType):
                
                null_ptr_equivalent = self.builder.inttoptr(right_value, left_type)
                value = self.builder.icmp_unsigned(node.operator, left_value, null_ptr_equivalent)
                return value, ir.IntType(1)

            if isinstance(right_type, ir.PointerType) and isinstance(left_type, ir.IntType):
                
                null_ptr_equivalent = self.builder.inttoptr(left_value, right_type)
                value = self.builder.icmp_unsigned(node.operator, right_value, null_ptr_equivalent)
                return value, ir.IntType(1)


        


        
        
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
        if isinstance(node.function, IdentifierLiteral) and node.function.value == "read_line":
            if node.arguments is None or len(node.arguments) != 1:
                return self.report_error("read_line() requires exactly one argument (a file pointer).")

            arg_resolved = self.resolve_value(node.arguments[0])
            if arg_resolved is None:
                return self.report_error("Could not resolve file pointer for read_line().")

            file_ptr, _ = arg_resolved
            fgets_func_res = self.env.lookup("read_line") 
            if fgets_func_res is None:
                return self.report_error("Internal error: C function 'fgets' not found.")

            fgets_func, ret_type = fgets_func_res

            
            buffer_size = 2048 
            buffer_type = ir.ArrayType(ir.IntType(8), buffer_size)
            buffer_alloca = self.builder.alloca(buffer_type, name="readline_buf")
            buffer_ptr = self.builder.gep(buffer_alloca,
                                        [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 0)],
                                        inbounds=True, name="readline_buf_ptr")

            size_arg = ir.Constant(ir.IntType(32), buffer_size)

            self.builder.call(fgets_func, [buffer_ptr, size_arg, file_ptr])

            
            return buffer_ptr, ret_type
        if isinstance(node.function, StructAccessExpression):
            access_node = cast(StructAccessExpression, node.function)
            method_name = access_node.member_name.value
            is_super_call = access_node.struct_name.type() == NodeType.SuperExpression
            
            instance_resolved = self.resolve_value(access_node.struct_name)
            if instance_resolved is None:
                return self.report_error("Could not resolve instance for method call.")
            instance_ptr, instance_type = instance_resolved
            
            if not (isinstance(instance_type, ir.PointerType) and isinstance(instance_type.pointee, ir.IdentifiedStructType)): # type: ignore
                return self.report_error("Method call on a non-class instance.")
            
            class_type = cast(ir.IdentifiedStructType, instance_type.pointee) # type: ignore
            
            search_class_name = class_type.name
            search_ptr = instance_ptr
            zero = ir.Constant(ir.IntType(32), 0)

            if is_super_call:
                current_class_name = self.builder.function.name.split('_')[0]
                parent_name = self.class_parents.get(current_class_name)
                if not parent_name:
                    return self.report_error(f"'super' call in class '{current_class_name}' which has no parent.")
                search_class_name = parent_name
                search_ptr = self.builder.gep(instance_ptr, [zero, zero], inbounds=True, name="super_ptr")

            
            found_method = False
            func_to_call = None
            ret_type = None
            num_args = len(params)

            while search_class_name:
                mangled_name = f"{search_class_name}_{method_name}_{num_args}"
                func_result = self.env.lookup(mangled_name)
                
                if func_result:
                    func_to_call, ret_type = func_result
                    found_method = True
                    break
                parent_name = self.class_parents.get(search_class_name)
                if parent_name:
                    search_ptr = self.builder.gep(search_ptr, [zero, zero], inbounds=True, name="parent_ptr_cast")
                search_class_name = parent_name
            
            if not found_method or func_to_call is None:
                return self.report_error(f"Class '{class_type.name}' has no method '{method_name}'.")

            func_to_call = cast(ir.Function, func_to_call)

           
            args_ir: list[ir.Value] = []
            for arg in params:
                resolved = self.resolve_value(arg)
                if resolved is not None:
                    args_ir.append(resolved[0])

            final_args = [search_ptr] + args_ir
            
            ret = self.builder.call(func_to_call, final_args)
            if ret_type is None:
                return self.report_error("Function return type could not be resolved.")

            return ret, ret_type

        
        if not isinstance(node.function, IdentifierLiteral) or node.function.value is None:
            self.report_error("CallExpression function must be an identifier with a name.")
            return None
        name: str = node.function.value

        if name == "reserve":
            if len(params) != 1:
                return self.report_error("reserve() requires exactly 1 size argument.")
            
            size_resolved = self.resolve_value(params[0])
            if size_resolved is None:
                return self.report_error("Could not resolve size for reserve().")
            
            data_size_bytes, _ = size_resolved

            element_type = self.type_map['int']
            element_size_bytes = ir.Constant(ir.IntType(32), 4)
            num_elements = self.builder.sdiv(data_size_bytes, element_size_bytes, "num_elements_from_size")

            header_size_bytes = ir.Constant(ir.IntType(32), 4)
            total_alloc_size = self.builder.add(header_size_bytes, data_size_bytes, "total_alloc_size")

            malloc_func_res = self.env.lookup("reserve")
            if malloc_func_res is None:
                return self.report_error("Internal error: C function 'malloc' not found.")
            
            malloc_func, _ = malloc_func_res

            raw_ptr = self.builder.call(malloc_func, [total_alloc_size], "raw_heap_ptr")

            len_ptr = self.builder.bitcast(raw_ptr, ir.IntType(32).as_pointer(), "len_header_ptr")
            self.builder.store(num_elements, len_ptr)

            data_ptr_i8 = self.builder.gep(raw_ptr, [header_size_bytes], inbounds=True, name="data_section_i8_ptr")
            
            typed_data_ptr = self.builder.bitcast(data_ptr_i8, ir.PointerType(element_type), "typed_data_ptr")
            if typed_data_ptr is None:
                self.report_error("Internal error: bitcast to typed pointer failed.")
                return None
            return typed_data_ptr, ir.PointerType(element_type)
        

        if name == "realloc":
            if len(params) != 2:
                self.report_error("realloc() requires exactly 2 arguments: a pointer and a new size.")
                return None

            
            array_ptr_resolved = self.resolve_value(params[0])
            if array_ptr_resolved is None:
                self.report_error("Could not resolve array pointer for realloc().")
                return None
            current_typed_data_ptr, var_type = array_ptr_resolved
            
            if not isinstance(var_type, ir.PointerType):
                return self.report_error(f"Cannot realloc a non-pointer type: '{var_type}'.")

            
            new_size_resolved = self.resolve_value(params[1])
            if new_size_resolved is None:
                return self.report_error("Could not resolve new size for realloc().")
            new_size_val, _ = new_size_resolved

            
            element_type = var_type.pointee # type: ignore
            
            if isinstance(element_type, ir.IntType): element_size_bytes = element_type.width // 8
            elif isinstance(element_type, ir.FloatType): element_size_bytes = 4
            elif isinstance(element_type, ir.DoubleType): element_size_bytes = 8
            else: element_size_bytes = 8 
            
            element_size_val = ir.Constant(ir.IntType(32), element_size_bytes)
            
            new_data_size_bytes = self.builder.mul(new_size_val, element_size_val, "new_data_size")
            header_size_val = ir.Constant(ir.IntType(32), 4)
            total_new_size_bytes = self.builder.add(new_data_size_bytes, header_size_val, "total_new_size")
            
            current_data_ptr_i8 = self.builder.bitcast(current_typed_data_ptr, ir.IntType(8).as_pointer(), "data_as_i8")
            header_offset = ir.Constant(ir.IntType(32), -4)
            current_header_ptr_i8 = self.builder.gep(current_data_ptr_i8, [header_offset], inbounds=True, name="current_header_ptr")
            
            realloc_func_res = self.env.lookup('realloc')
            if realloc_func_res is None: 
                return self.report_error("Internal error: C function 'realloc' not found.")
            realloc_func, _ = realloc_func_res
            
            new_header_ptr_i8 = self.builder.call(realloc_func, [current_header_ptr_i8, total_new_size_bytes], "new_block_ptr")
            
            new_len_ptr = self.builder.bitcast(new_header_ptr_i8, ir.IntType(32).as_pointer(), "new_header_len_ptr")
            self.builder.store(new_size_val, new_len_ptr)
            
            new_data_ptr_i8 = self.builder.gep(new_header_ptr_i8, [header_size_val], inbounds=True, name="new_data_i8_ptr")
            
            new_typed_data_ptr = self.builder.bitcast(new_data_ptr_i8, current_typed_data_ptr.type, "new_typed_data_ptr") # type: ignore
            if new_typed_data_ptr is None:
                self.report_error("Internal error: bitcast to typed pointer failed during realloc.")
                return None
            return new_typed_data_ptr, new_typed_data_ptr.type


        vector_struct_type = self.struct_types.get("vector")
        zero = ir.Constant(ir.IntType(32), 0)
        one = ir.Constant(ir.IntType(32), 1)
        double_type = ir.DoubleType()

        if name == "hypocrisy":
            if len(params) != 2:
                self.report_error("hypocrisy() requires exactly two arguments: seen and truth.")
                return None

            seen_res = self.resolve_value(params[0])
            truth_res = self.resolve_value(params[1])

            if seen_res is None or truth_res is None:
                self.report_error("Could not resolve arguments for hypocrisy().")
                return None

            seen_val, seen_type = seen_res
            truth_val, truth_type = truth_res

            if seen_type != truth_type:
                self.report_error(f"hypocrisy() values must be of the same type. Got {seen_type} and {truth_type}.")
                return None

            type_name_str = str(seen_type).replace("%", "").replace(" ", "_").replace("*", "ptr")
            struct_type_name = f"hypocrisy_{type_name_str}"
            
            hypocrisy_struct_type = self.struct_types.get(struct_type_name)
            if hypocrisy_struct_type is None:
                hypocrisy_struct_type = self.module.context.get_identified_type(struct_type_name)
                hypocrisy_struct_type.set_body(seen_type, truth_type)
                self.struct_types[struct_type_name] = hypocrisy_struct_type

            instance_ptr = self.builder.alloca(hypocrisy_struct_type, name="hypocrisy_instance")

            seen_field_ptr = self.builder.gep(instance_ptr, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 0)], inbounds=True, name="seen_ptr")
            self.builder.store(seen_val, seen_field_ptr)

            truth_field_ptr = self.builder.gep(instance_ptr, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 1)], inbounds=True, name="truth_ptr")
            self.builder.store(truth_val, truth_field_ptr)

            return instance_ptr, ir.PointerType(hypocrisy_struct_type)

        

        if name == "vector":
            if len(params) != 2:
                return self.report_error("vector() constructor needs 2 args: size (int) and elements (array).")
            
            size_res = self.resolve_value(params[0])
            elems_res = self.resolve_value(params[1])
            if size_res is None or elems_res is None:
                return self.report_error("Could not resolve arguments for vector().")
            
            size_val, _ = size_res
            elems_array_ptr, _ = elems_res
            
            malloc_func, _ = self.env.lookup("reserve") # type: ignore
            alloc_size = self.builder.mul(size_val, ir.Constant(ir.IntType(32), 8))
            data_ptr = self.builder.call(malloc_func, [alloc_size])
            data_ptr = self.builder.bitcast(data_ptr, ir.PointerType(double_type))
            
            vec_ptr = self.builder.alloca(vector_struct_type, name="vector_instance")
            self.builder.store(data_ptr, self.builder.gep(vec_ptr, [zero, zero], inbounds=True))
            self.builder.store(size_val, self.builder.gep(vec_ptr, [zero, one], inbounds=True))
            
            loop_cond_v = self.builder.append_basic_block('loop_cond_v_init')
            loop_body_v = self.builder.append_basic_block('loop_body_v_init')
            loop_exit_v = self.builder.append_basic_block('loop_exit_v_init')
            
            counter_ptr_v = self.builder.alloca(ir.IntType(32), name='i_v')
            
            self.builder.store(zero, counter_ptr_v)
            self.builder.branch(loop_cond_v)
            self.builder.position_at_start(loop_cond_v)
            
            i_v = self.builder.load(counter_ptr_v)
            cond_v = self.builder.icmp_signed('<', i_v, size_val)
           
            self.builder.cbranch(cond_v, loop_body_v, loop_exit_v)
            self.builder.position_at_start(loop_body_v)
           
            src_elem_ptr = self.builder.gep(elems_array_ptr, [i_v], inbounds=True)
            
            elem_val = self.builder.load(src_elem_ptr)
            promoted_val = elem_val
           
            if isinstance(elem_val.type, ir.IntType):
                promoted_val = self.builder.sitofp(elem_val, double_type)
           
            elif isinstance(elem_val.type, ir.FloatType):
                promoted_val = self.builder.fpext(elem_val, double_type)
           
            self.builder.store(promoted_val, self.builder.gep(data_ptr, [i_v], inbounds=True))
            next_i_v = self.builder.add(i_v, one)
           
            self.builder.store(next_i_v, counter_ptr_v)
            self.builder.branch(loop_cond_v)
            self.builder.position_at_start(loop_exit_v)
           
            return vec_ptr, ir.PointerType(vector_struct_type)


        if name == "dot":
            if len(params) != 2:
                return self.report_error("dot() requires exactly 2 vector arguments.")
            
            v1_res = self.resolve_value(params[0])
            v2_res = self.resolve_value(params[1])
            
            if not v1_res or not v2_res:
                return None
            
            v1_ptr, v1_type = v1_res
            v2_ptr, v2_type = v2_res
            if not (isinstance(v1_type, ir.PointerType) and v1_type.pointee == vector_struct_type and # type: ignore
                    isinstance(v2_type, ir.PointerType) and v2_type.pointee == vector_struct_type): # type: ignore
                
                return self.report_error("dot() arguments must be vectors.")

            size = self.builder.load(self.builder.gep(v1_ptr, [zero, one], inbounds=True))
            v1_data = self.builder.load(self.builder.gep(v1_ptr, [zero, zero], inbounds=True))
            v2_data = self.builder.load(self.builder.gep(v2_ptr, [zero, zero], inbounds=True))
            
            accumulator = self.builder.alloca(double_type, name="dot_sum")
            self.builder.store(ir.Constant(double_type, 0.0), accumulator)

            loop_cond = self.builder.append_basic_block('dot_loop_cond')
            loop_body = self.builder.append_basic_block('dot_loop_body')
            loop_exit = self.builder.append_basic_block('dot_loop_exit')
            
            counter = self.builder.alloca(ir.IntType(32), name='i_dot')
            self.builder.store(zero, counter)
            self.builder.branch(loop_cond)
            self.builder.position_at_start(loop_cond)
            
            i = self.builder.load(counter)
            self.builder.cbranch(self.builder.icmp_signed('<', i, size), loop_body, loop_exit)
            self.builder.position_at_start(loop_body)
            
            e1 = self.builder.load(self.builder.gep(v1_data, [i], inbounds=True))
            e2 = self.builder.load(self.builder.gep(v2_data, [i], inbounds=True))
            
            product = self.builder.fmul(e1, e2)
            current_sum = self.builder.load(accumulator)
            new_sum = self.builder.fadd(current_sum, product)
            
            self.builder.store(new_sum, accumulator)
            self.builder.store(self.builder.add(i, one), counter)
            self.builder.branch(loop_cond)
            self.builder.position_at_start(loop_exit)
            
            return self.builder.load(accumulator), double_type

        if name == "cross":
            if len(params) != 2:
                return self.report_error("cross() requires exactly 2 vector arguments.")

            v1_res = self.resolve_value(params[0])
            v2_res = self.resolve_value(params[1])

            if not v1_res or not v2_res:
                return None

            v1_ptr, v1_type = v1_res
            v2_ptr, v2_type = v2_res

        
            if not (isinstance(v1_type, ir.PointerType) and v1_type.pointee == vector_struct_type and # type: ignore
                    isinstance(v2_type, ir.PointerType) and v2_type.pointee == vector_struct_type): # type: ignore
                return self.report_error("cross() arguments must be vectors.")

            
            v1_data = self.builder.load(self.builder.gep(v1_ptr, [zero, zero], inbounds=True))
            v2_data = self.builder.load(self.builder.gep(v2_ptr, [zero, zero], inbounds=True))

            
            x1 = self.builder.load(self.builder.gep(v1_data, [ir.Constant(ir.IntType(32), 0)], inbounds=True))
            y1 = self.builder.load(self.builder.gep(v1_data, [ir.Constant(ir.IntType(32), 1)], inbounds=True))
            z1 = self.builder.load(self.builder.gep(v1_data, [ir.Constant(ir.IntType(32), 2)], inbounds=True))

            x2 = self.builder.load(self.builder.gep(v2_data, [ir.Constant(ir.IntType(32), 0)], inbounds=True))
            y2 = self.builder.load(self.builder.gep(v2_data, [ir.Constant(ir.IntType(32), 1)], inbounds=True))
            z2 = self.builder.load(self.builder.gep(v2_data, [ir.Constant(ir.IntType(32), 2)], inbounds=True))

           
            cx = self.builder.fsub(self.builder.fmul(y1, z2), self.builder.fmul(z1, y2), "cx")
            cy = self.builder.fsub(self.builder.fmul(z1, x2), self.builder.fmul(x1, z2), "cy")
            cz = self.builder.fsub(self.builder.fmul(x1, y2), self.builder.fmul(y1, x2), "cz")

            lookup_result = self.env.lookup("reserve")
            if lookup_result is None:
                return self.report_error("Builtin 'reserve' not found in environment.")

            malloc_func, malloc_type = lookup_result

            alloc_size = ir.Constant(ir.IntType(32), 3 * 8) 
            new_data_ptr = self.builder.call(malloc_func, [alloc_size])
            new_data_ptr = self.builder.bitcast(new_data_ptr, ir.PointerType(double_type))

            
            result_vec_ptr = self.builder.alloca(vector_struct_type, name="cross_result_vec")
            
            self.builder.store(new_data_ptr, self.builder.gep(result_vec_ptr, [zero, zero], inbounds=True))
            self.builder.store(ir.Constant(ir.IntType(32), 3), self.builder.gep(result_vec_ptr, [zero, one], inbounds=True))

            self.builder.store(cx, self.builder.gep(new_data_ptr, [ir.Constant(ir.IntType(32), 0)], inbounds=True))
            self.builder.store(cy, self.builder.gep(new_data_ptr, [ir.Constant(ir.IntType(32), 1)], inbounds=True))
            self.builder.store(cz, self.builder.gep(new_data_ptr, [ir.Constant(ir.IntType(32), 2)], inbounds=True))

            return result_vec_ptr, ir.PointerType(vector_struct_type)
        
        
        if name == "magnitude": 
            if len(params) != 1: 
                return self.report_error("abs() requires one argument.")
            arg_res = self.resolve_value(params[0])
            
            if not arg_res: 
                return None
            arg_val, arg_type = arg_res
            
            if isinstance(arg_type, ir.PointerType) and arg_type.pointee == vector_struct_type: # type: ignore
                vec_ptr = arg_val
                size = self.builder.load(self.builder.gep(vec_ptr, [zero, one], inbounds=True))
                vec_data = self.builder.load(self.builder.gep(vec_ptr, [zero, zero], inbounds=True))
                
                sum_sq = self.builder.alloca(double_type, name="sum_sq")
                self.builder.store(ir.Constant(double_type, 0.0), sum_sq)

                loop_cond = self.builder.append_basic_block('abs_loop_cond')
                loop_body = self.builder.append_basic_block('abs_loop_body')
                loop_exit = self.builder.append_basic_block('abs_loop_exit')
                
                
                counter = self.builder.alloca(ir.IntType(32), name='i_abs')
                
                self.builder.store(zero, counter)
                self.builder.branch(loop_cond)
                self.builder.position_at_start(loop_cond)
                
                i = self.builder.load(counter)
                self.builder.cbranch(self.builder.icmp_signed('<', i, size), loop_body, loop_exit)
                self.builder.position_at_start(loop_body)
                
                elem = self.builder.load(self.builder.gep(vec_data, [i], inbounds=True))
                elem_sq = self.builder.fmul(elem, elem)
                
                current_sum = self.builder.load(sum_sq)
                new_sum = self.builder.fadd(current_sum, elem_sq)
                
                self.builder.store(new_sum, sum_sq)
                self.builder.store(self.builder.add(i, one), counter)
                self.builder.branch(loop_cond)
                self.builder.position_at_start(loop_exit)
                
                final_sum_sq = self.builder.load(sum_sq)
                sqrt_func, _ = self.env.lookup('sqrt') # type: ignore
                magnitude = self.builder.call(sqrt_func, [final_sum_sq])
                
                return magnitude, double_type
            

        if name == "complex":
            if len(params) != 2:
                return self.report_error("complex() constructor requires 2 arguments: real and imaginary.")

            real_res = self.resolve_value(params[0])
            imag_res = self.resolve_value(params[1])

            if real_res is None or imag_res is None:
                return self.report_error("Could not resolve arguments for complex() constructor.")

            real_val, r_type = real_res
            imag_val, i_type = imag_res

            double_type = ir.DoubleType()
            if not isinstance(r_type, ir.DoubleType):
                real_val = self.builder.sitofp(real_val, double_type) if isinstance(r_type, ir.IntType) else self.builder.fpext(real_val, double_type)
            if not isinstance(i_type, ir.DoubleType):
                imag_val = self.builder.sitofp(imag_val, double_type) if isinstance(i_type, ir.IntType) else self.builder.fpext(imag_val, double_type)

            complex_type = self.struct_types["complex"]
            instance_ptr = self.builder.alloca(complex_type, name="complex_instance")

            real_ptr = self.builder.gep(instance_ptr, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 0)], inbounds=True, name="real_ptr")
            self.builder.store(real_val, real_ptr)

            imag_ptr = self.builder.gep(instance_ptr, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 1)], inbounds=True, name="imag_ptr")
            self.builder.store(imag_val, imag_ptr)

            return instance_ptr, ir.PointerType(complex_type)

        
        if name == "abs":
            if len(params) != 1:
                return self.report_error("abs() requires exactly one argument.")

            arg_res = self.resolve_value(params[0])
            if arg_res is None:
                return self.report_error("Could not resolve argument for abs().")
            arg_val, arg_type = arg_res
            
            is_complex = isinstance(arg_type, ir.PointerType) and isinstance(arg_type.pointee, ir.IdentifiedStructType) and arg_type.pointee.name == "complex" # type: ignore
            if not is_complex:
                return self.report_error("abs() is currently only implemented for complex numbers.")

            real_ptr = self.builder.gep(arg_val, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 0)], inbounds=True)
            imag_ptr = self.builder.gep(arg_val, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 1)], inbounds=True)
            
            real_val = self.builder.load(real_ptr)
            imag_val = self.builder.load(imag_ptr)

            real_sq = self.builder.fmul(real_val, real_val, "real_sq")
            imag_sq = self.builder.fmul(imag_val, imag_val, "imag_sq")
            sum_sq = self.builder.fadd(real_sq, imag_sq, "sum_sq")

            sqrt_func_res = self.env.lookup('sqrt')
            if sqrt_func_res is None:
                return self.report_error("sqrt function not found for abs() calculation.")
            sqrt_func, _ = sqrt_func_res
            
            magnitude = self.builder.call(sqrt_func, [sum_sq], "magnitude")
            
            return magnitude, ir.DoubleType()
        

        if name in ('cot', 'sec', 'cosec'):
            if len(params) != 1:
                self.report_error(f"{name}() requires exactly one double argument.")
                return None
            
            arg_res = self.resolve_value(params[0])
            if arg_res is None:
                self.report_error(f"Could not resolve argument for {name}().")
                return None
            angle_val, angle_type = arg_res
            
            if not isinstance(angle_type, ir.DoubleType):
                if isinstance(angle_type, ir.FloatType):
                    angle_val = self.builder.fpext(angle_val, ir.DoubleType())
                elif isinstance(angle_type, ir.IntType):
                    angle_val = self.builder.sitofp(angle_val, ir.DoubleType())
                else:
                    self.report_error(f"{name}() requires a numeric argument.")
                    return None

            res = self.env.lookup("sin")
            if res is None:
                return self.report_error("Function 'sin' not found in environment.")
            sin_func, _ = res

            res_cos = self.env.lookup("cos")
            if res_cos is None:
                return self.report_error("Function 'cos' not found in environment.")
            cos_func, _ = res_cos



            one = ir.Constant(ir.DoubleType(), 1.0)
            
            if name == 'cosec':
                sin_val = self.builder.call(sin_func, [angle_val])
                result = self.builder.fdiv(one, sin_val)
            elif name == 'sec':
                cos_val = self.builder.call(cos_func, [angle_val])
                result = self.builder.fdiv(one, cos_val)
            elif name == 'cot':
                sin_val = self.builder.call(sin_func, [angle_val])
                cos_val = self.builder.call(cos_func, [angle_val])
                result = self.builder.fdiv(cos_val, sin_val)
            
            if result is None:
                return None
            return result, ir.DoubleType()


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



        #print(f">>> CallExpression: calling function '{name}' with {len(params)} arguments")
        
        if name == "print":
            if not params:
                return self.report_error("print() requires at least one argument.")

            printf_func, _ = self.env.lookup("print") # type: ignore
            zero = ir.Constant(ir.IntType(32), 0)

            for arg_expr in params:
                result = self.resolve_value(arg_expr)
                if result is None:
                    self.report_error("Failed to resolve print argument.")
                    continue
                
                val, val_type = result
                is_fixed_array = (
                    isinstance(val_type, ir.PointerType) and 
                    isinstance(getattr(val_type, 'pointee', None), ir.ArrayType)
                )

                vector_struct_type = self.struct_types.get("vector")
                is_vector = (vector_struct_type and 
                             isinstance(val_type, ir.PointerType) and 
                             val_type.pointee == vector_struct_type) # type: ignore

                if is_vector:
                    self.builder.call(self.print_vector_func, [val])
                    continue

                if is_fixed_array:
                    array_len = val_type.pointee.count # type: ignore
                    element_type = val_type.pointee.element # type: ignore

                    open_bracket_fmt, _ = self.convert_string("[")
                    open_bracket_ptr = self.builder.gep(open_bracket_fmt, [zero, zero], inbounds=True)
                    self.builder.call(printf_func, [open_bracket_ptr])

                    loop_entry = self.builder.append_basic_block("fixed_array_print_entry")
                    loop_body = self.builder.append_basic_block("fixed_array_print_body")
                    loop_exit = self.builder.append_basic_block("fixed_array_print_exit")

                    counter_ptr = self.builder.alloca(ir.IntType(32), name='i_fixed_array_print')
                    self.builder.store(ir.Constant(ir.IntType(32), 0), counter_ptr)
                    self.builder.branch(loop_entry)

                    self.builder.position_at_start(loop_entry)
                    i = self.builder.load(counter_ptr)
                    cond = self.builder.icmp_signed('<', i, ir.Constant(ir.IntType(32), array_len))
                    self.builder.cbranch(cond, loop_body, loop_exit)

                    self.builder.position_at_start(loop_body)
                    is_not_first = self.builder.icmp_signed('!=', i, ir.Constant(ir.IntType(32), 0))
                    with self.builder.if_then(is_not_first):
                        separator_fmt, _ = self.convert_string(", ")
                        separator_ptr = self.builder.gep(separator_fmt, [zero, zero], inbounds=True)
                        self.builder.call(printf_func, [separator_ptr])
                    
                    element_ptr_gep = self.builder.gep(val, [zero, i], inbounds=True)
                    element_val = self.builder.load(element_ptr_gep)

                    elem_format_str = ""
                    arg_to_pass = element_val
                    
                    if isinstance(element_type, ir.IntType) and element_type.width == 32:
                        elem_format_str = "%d"
                    elif isinstance(element_type, ir.DoubleType):
                        elem_format_str = "%f"
                    elif isinstance(element_type, ir.FloatType):
                        elem_format_str = "%f"
                        
                        arg_to_pass = self.builder.fpext(element_val, ir.DoubleType())
                    elif isinstance(element_type, ir.IntType) and element_type.width == 1:
                        elem_format_str = "%s"
                        true_ptr = self.builder.gep(self.true_str, [zero, zero], inbounds=True)
                        false_ptr = self.builder.gep(self.false_str, [zero, zero], inbounds=True)
                        arg_to_pass = self.builder.select(element_val, true_ptr, false_ptr)
                    elif isinstance(element_type, ir.PointerType) and isinstance(element_type.pointee, ir.IntType) and element_type.pointee.width == 8: # type: ignore
                        
                        elem_format_str = "\"%s\""
                    
                    if elem_format_str:
                        fmt_g, _ = self.convert_string(elem_format_str)
                        fmt_p = self.builder.gep(fmt_g, [zero, zero], inbounds=True)
                        self.builder.call(printf_func, [fmt_p, arg_to_pass])
                    else:
                        self.report_error(f"Printing array with element type {element_type} is not supported.")
                    
                    next_i = self.builder.add(i, ir.Constant(ir.IntType(32), 1))
                    self.builder.store(next_i, counter_ptr)
                    self.builder.branch(loop_entry)

                    self.builder.position_at_start(loop_exit)
                    close_bracket_fmt, _ = self.convert_string("]")
                    close_bracket_ptr = self.builder.gep(close_bracket_fmt, [zero, zero], inbounds=True)
                    self.builder.call(printf_func, [close_bracket_ptr])
                    continue

                is_dynamic_array = (
                    isinstance(val_type, ir.PointerType) and 
                    val_type != ir.IntType(8).as_pointer() and 
                    isinstance(val_type.pointee, (ir.IntType, ir.FloatType, ir.DoubleType, ir.PointerType)) # type: ignore
                )

                if is_dynamic_array:
                    data_ptr = val
                    element_type = val_type.pointee # type: ignore

                    data_ptr_as_i8 = self.builder.bitcast(data_ptr, ir.IntType(8).as_pointer())
                    header_offset = ir.Constant(ir.IntType(32), -4)
                    len_header_ptr_i8 = self.builder.gep(data_ptr_as_i8, [header_offset], inbounds=True)
                    len_ptr = self.builder.bitcast(len_header_ptr_i8, ir.IntType(32).as_pointer())
                    array_len = self.builder.load(len_ptr, "dyn_array_len")

                    open_bracket_fmt, _ = self.convert_string("[")
                    open_bracket_ptr = self.builder.gep(open_bracket_fmt, [zero, zero], inbounds=True)
                    self.builder.call(printf_func, [open_bracket_ptr])

                    loop_entry = self.builder.append_basic_block("dyn_array_print_entry")
                    loop_body = self.builder.append_basic_block("dyn_array_print_body")
                    loop_exit = self.builder.append_basic_block("dyn_array_print_exit")

                    counter_ptr = self.builder.alloca(ir.IntType(32), name='i_dyn_array_print')
                    self.builder.store(ir.Constant(ir.IntType(32), 0), counter_ptr)
                    self.builder.branch(loop_entry)

                    self.builder.position_at_start(loop_entry)
                    i = self.builder.load(counter_ptr)
                    cond = self.builder.icmp_signed('<', i, array_len)
                    self.builder.cbranch(cond, loop_body, loop_exit)

                    self.builder.position_at_start(loop_body)
                    is_not_first = self.builder.icmp_signed('!=', i, ir.Constant(ir.IntType(32), 0))
                    with self.builder.if_then(is_not_first):
                        separator_fmt, _ = self.convert_string(", ")
                        separator_ptr = self.builder.gep(separator_fmt, [zero, zero], inbounds=True)
                        self.builder.call(printf_func, [separator_ptr])
                    
                    element_ptr_gep = self.builder.gep(data_ptr, [i], inbounds=True)
                    element_val = self.builder.load(element_ptr_gep)

                    
                    elem_format_str = ""
                    arg_to_pass = element_val
                    
                    if isinstance(element_type, ir.IntType) and element_type.width == 32:
                        elem_format_str = "%d"
                    elif isinstance(element_type, ir.DoubleType):
                        elem_format_str = "%f"
                    elif isinstance(element_type, ir.FloatType):
                        elem_format_str = "%f"
                        
                        arg_to_pass = self.builder.fpext(element_val, ir.DoubleType())
                    elif isinstance(element_type, ir.IntType) and element_type.width == 1:
                        elem_format_str = "%s"
                        true_ptr = self.builder.gep(self.true_str, [zero, zero], inbounds=True)
                        false_ptr = self.builder.gep(self.false_str, [zero, zero], inbounds=True)
                        arg_to_pass = self.builder.select(element_val, true_ptr, false_ptr)
                    elif isinstance(element_type, ir.PointerType) and isinstance(element_type.pointee, ir.IntType) and element_type.pointee.width == 8: # type: ignore
                        
                        elem_format_str = "\"%s\""
                    
                    if elem_format_str:
                        fmt_g, _ = self.convert_string(elem_format_str)
                        fmt_p = self.builder.gep(fmt_g, [zero, zero], inbounds=True)
                        self.builder.call(printf_func, [fmt_p, arg_to_pass])
                    else:
                        self.report_error(f"Printing array with element type {element_type} is not supported.")
                    
                    next_i = self.builder.add(i, ir.Constant(ir.IntType(32), 1))
                    self.builder.store(next_i, counter_ptr)
                    self.builder.branch(loop_entry)

                    self.builder.position_at_start(loop_exit)
                    close_bracket_fmt, _ = self.convert_string("]")
                    close_bracket_ptr = self.builder.gep(close_bracket_fmt, [zero, zero], inbounds=True)
                    self.builder.call(printf_func, [close_bracket_ptr])
                    continue

                
                format_str = ""
                arg_to_pass = val

                if isinstance(val_type, ir.PointerType) and isinstance(val_type.pointee, ir.IntType) and val_type.pointee.width == 8: # type: ignore
                    format_str = "%s"
                elif isinstance(val_type, ir.IntType) and val_type.width == 32:
                    format_str = "%d"
                elif isinstance(val_type, ir.DoubleType):
                    format_str = "%f"
                elif isinstance(val_type, ir.FloatType):
                    format_str = "%f"
                    arg_to_pass = self.builder.fpext(val, ir.DoubleType())
                elif isinstance(val_type, ir.IntType) and val_type.width == 1:
                    format_str = "%s"
                    true_ptr = self.builder.gep(self.true_str, [zero, zero], inbounds=True)
                    false_ptr = self.builder.gep(self.false_str, [zero, zero], inbounds=True)
                    arg_to_pass = self.builder.select(val, true_ptr, false_ptr)

                if format_str:
                    fmt_global, _ = self.convert_string(format_str)
                    fmt_ptr = self.builder.gep(fmt_global, [zero, zero], inbounds=True)
                    self.builder.call(printf_func, [fmt_ptr, arg_to_pass])
                else:
                    self.report_error(f"Unsupported type for print(): {val_type}")

            newline_fmt, _ = self.convert_string("\n")
            newline_ptr = self.builder.gep(newline_fmt, [zero, zero], inbounds=True)
            self.builder.call(printf_func, [newline_ptr])
            
            return ir.Constant(ir.IntType(32), 0), ir.IntType(32)
      
        elif name == "free":
            if len(params) != 1:
                self.report_error("free() requires exactly one pointer argument.")
                return None
            
            arg_result = self.resolve_value(params[0])
            if arg_result is None:
                self.report_error("Could not resolve argument for free().")
                return None
            
            data_ptr, _ = arg_result

            ptr_val_i8 = self.builder.bitcast(data_ptr, ir.IntType(8).as_pointer())
            
            header_offset = ir.Constant(ir.IntType(32), -4)
            block_start_ptr = self.builder.gep(ptr_val_i8, [header_offset], inbounds=True, name="block_start_ptr")

            free_func_result = self.env.lookup("free")
            if free_func_result is None:
                self.report_error("Built-in function 'free' not found.")
                return None

            free_func, free_ret_type = free_func_result
            
            ret = self.builder.call(free_func, [block_start_ptr])
            return ret, free_ret_type

        
        elif name == "len":
            if len(params) != 1:
                self.report_error("len() requires exactly 1 argument.")
                return None

            arg_resolved = self.resolve_value(params[0])
            if arg_resolved is None:
                self.report_error("Could not resolve argument for len().")
                return None

            data_ptr, data_ptr_type = arg_resolved

            if isinstance(data_ptr_type, ir.PointerType):
                data_ptr_i8 = self.builder.bitcast(data_ptr, ir.IntType(8).as_pointer(), "data_ptr_as_i8")
                
                header_offset = ir.Constant(ir.IntType(32), -4)
                len_header_ptr_i8 = self.builder.gep(data_ptr_i8, [header_offset], inbounds=True, name="len_header_i8_ptr")
                
                len_ptr = self.builder.bitcast(len_header_ptr_i8, ir.IntType(32).as_pointer(), name="len_ptr")

                
                array_len = self.builder.load(len_ptr, "array_len")
                return array_len, self.type_map['int']

            if isinstance(data_ptr_type, ir.ArrayType):
                return ir.Constant(self.type_map['int'], data_ptr_type.count), self.type_map['int']

            self.report_error("len() only works on array types.")
            return None

        result = self.env.lookup(name)
        if result is None:
            if name in self.generic_functions:
                generic_ast = self.generic_functions[name]
                
                arg_vals: list[ir.Value] = []
                arg_types: list[ir.Type] = []
                for arg_expr in params:
                    resolved_arg = self.resolve_value(arg_expr)
                    if resolved_arg is None:
                        self.report_error(f"Could not resolve argument for generic call to '{name}'")
                        return None
                    val, typ = resolved_arg
                    arg_vals.append(val)
                    arg_types.append(typ)
                
                
                type_suffixes = [str(t).replace('%', '').replace(' ', '_').replace('*', 'ptr') for t in arg_types]
                mangled_name = f"{name}_{'_'.join(type_suffixes)}"

                
                instance_result = self.env.lookup(mangled_name)
                if instance_result:
                    func, ret_type = instance_result
                    return self.builder.call(func, arg_vals), ret_type
                
                
                new_func_result = self._instantiate_and_compile_generic_function(generic_ast, mangled_name, arg_types)
                if new_func_result is None:
                    self.report_error(f"Failed to create a version of function '{name}' for types: {type_suffixes}")
                    return None
                
                new_func, ret_type = new_func_result
                return self.builder.call(new_func, arg_vals), ret_type
            self.report_error(f"Function '{name}' not found in environment.")
            return None
        assert result is not None  
        func, ret_type = result

        if name == "write":
            
            params = [params[1], params[0]] 

     
        func = cast(ir.Function, func)
        expected_arg_types: list[ir.Type] = list(func.function_type.args)

     
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

    def visit_as_expression(self, node: "AsExpression") -> Optional[tuple[ir.Value, ir.Type]]:
        var_resolved = self.resolve_value(node.variable)
        if var_resolved is None:
            self.report_error("Could not resolve hypocrisy variable in 'as' expression.")
            return None
        
        struct_ptr, ptr_type = var_resolved

        if not (isinstance(ptr_type, ir.PointerType) and 
                isinstance(ptr_type.pointee, ir.IdentifiedStructType) and  # type: ignore
                ptr_type.pointee.name.startswith("hypocrisy_")): # type: ignore
            self.report_error("The 'as' operator can only be used on hypocrisy variables.")
            return None

        specifier = node.specifier.value
        index = 0 if specifier == "seen" else 1

        field_ptr = self.builder.gep(
            struct_ptr,
            [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), index)],
            inbounds=True,
            name=f"{specifier}_ptr"
        )
        
        loaded_value = self.builder.load(field_ptr, name=specifier or "tmp")
        return loaded_value, loaded_value.type
        
    
    def __define_print_vector_helper(self):
       
        vector_ptr_type = ir.PointerType(self.struct_types["vector"])
        fnty = ir.FunctionType(ir.VoidType(), [vector_ptr_type])
        self.print_vector_func = ir.Function(self.module, fnty, 'print_vector')

        prev_builder = self.builder
        block = self.print_vector_func.append_basic_block('entry')
        self.builder = ir.IRBuilder(block)

        vec_ptr, = self.print_vector_func.args

        size_ptr = self.builder.gep(vec_ptr, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 1)], inbounds=True)
        data_ptr_ptr = self.builder.gep(vec_ptr, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 0)], inbounds=True)
        size = self.builder.load(size_ptr)
        data_ptr = self.builder.load(data_ptr_ptr)

        lookup_result = self.env.lookup("print")
        if lookup_result is None:
            raise RuntimeError("Builtin 'print' not found during compiler initialization.")

        printf_func = lookup_result[0]


        open_bracket_fmt, _ = self.convert_string("[")
        close_bracket_fmt, _ = self.convert_string("]")
        element_fmt, _ = self.convert_string("%f")
        separator_fmt, _ = self.convert_string(", ")
        
        open_bracket_ptr = self.builder.gep(open_bracket_fmt, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 0)], inbounds=True)
        close_bracket_ptr = self.builder.gep(close_bracket_fmt, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 0)], inbounds=True)
        element_ptr = self.builder.gep(element_fmt, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 0)], inbounds=True)
        separator_ptr = self.builder.gep(separator_fmt, [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 0)], inbounds=True)

        self.builder.call(printf_func, [open_bracket_ptr])

        loop_cond = self.builder.append_basic_block('loop_cond_print')
        loop_body = self.builder.append_basic_block('loop_body_print')
        loop_exit = self.builder.append_basic_block('loop_exit_print')
        
        counter_ptr = self.builder.alloca(ir.IntType(32), name='i')
        self.builder.store(ir.Constant(ir.IntType(32), 0), counter_ptr)
        self.builder.branch(loop_cond)

        self.builder.position_at_start(loop_cond)
        i = self.builder.load(counter_ptr)
        cond = self.builder.icmp_signed('<', i, size)
        self.builder.cbranch(cond, loop_body, loop_exit)

        self.builder.position_at_start(loop_body)
        
        is_first = self.builder.icmp_signed('==', i, ir.Constant(ir.IntType(32), 0))
        with self.builder.if_then(is_first, likely=False):
            pass 
        with self.builder.if_else(is_first) as (then, otherwise):
            with then:
                pass
            with otherwise:
                self.builder.call(printf_func, [separator_ptr])

        
        elem_ptr = self.builder.gep(data_ptr, [i], inbounds=True)
        elem = self.builder.load(elem_ptr)
        self.builder.call(printf_func, [element_ptr, elem])

        next_i = self.builder.add(i, ir.Constant(ir.IntType(32), 1))
        self.builder.store(next_i, counter_ptr)
        self.builder.branch(loop_cond)

       
        self.builder.position_at_start(loop_exit)
        self.builder.call(printf_func, [close_bracket_ptr])
        self.builder.ret_void()

  
        self.builder = prev_builder

    def _instantiate_and_compile_generic_function(
        self,
        node: FunctionStatement,
        mangled_name: str,
        param_types: list[ir.Type]
    ) -> Optional[tuple[ir.Function, ir.Type]]:

        if node.name is None or node.name.value is None or node.body is None:
            return None

        name: str = node.name.value
        body: BlockStatement = node.body
        params: list[FunctionParameter] = node.parameters or []
        param_names: list[str] = [p.name for p in params if p.name]

        global_env = self._get_global_env()

        dummy_func_type = ir.FunctionType(ir.VoidType(), param_types)
        dummy_module = ir.Module(name=f"{mangled_name}_dummy")
        dummy_func = ir.Function(dummy_module, dummy_func_type, name=f"{mangled_name}_dummy_func")
        dummy_block = dummy_func.append_basic_block("entry")

        caller_builder = self.builder
        caller_env = self.env
        self.builder = ir.IRBuilder(dummy_block)
        self.env = Environment(parent=global_env)

        self.env.define(name, dummy_func, ir.VoidType())

        for i, param_name in enumerate(param_names):
            if isinstance(param_types[i], ir.PointerType) and isinstance(param_types[i].pointee, ir.ArrayType): # type: ignore
                null_ptr_for_type_checking = ir.Constant(param_types[i], None)
                self.env.define(param_name, null_ptr_for_type_checking, param_types[i])
            else:
                dummy_alloca = self.builder.alloca(param_types[i])
                self.env.define(param_name, dummy_alloca, param_types[i])
        
        self.compile(body)

        inferred_type = "void"
        inferred_ir_type_actual = self._find_and_infer_return_type(body)

        if node.return_type:
            inferred_type = node.return_type
        elif inferred_ir_type_actual:
            if isinstance(inferred_ir_type_actual, ir.IntType) and inferred_ir_type_actual.width == 1: inferred_type = "bool"
            elif isinstance(inferred_ir_type_actual, ir.IntType): inferred_type = "int"
            elif isinstance(inferred_ir_type_actual, ir.FloatType): inferred_type = "float"
            elif isinstance(inferred_ir_type_actual, ir.DoubleType): inferred_type = "double"
            elif isinstance(inferred_ir_type_actual, ir.PointerType): inferred_type = "array"

        if inferred_type == "array" and inferred_ir_type_actual is not None:
             return_ir_type = inferred_ir_type_actual
        else:
             return_ir_type = self.type_map.get(inferred_type, ir.IntType(32).as_pointer() if inferred_type == "array" else ir.VoidType())

        self.builder = caller_builder
        self.env = caller_env

        func_type = ir.FunctionType(return_ir_type, param_types)
        func = ir.Function(self.module, func_type, name=mangled_name)

        global_env.define(mangled_name, func, return_ir_type)

        caller_builder = self.builder
        caller_env = self.env
        was_in_main = self.is_in_main

        self.is_in_main = False
        block = func.append_basic_block(f'{mangled_name}_entry')
        self.builder = ir.IRBuilder(block)
        
        
        self.env = Environment(parent=caller_env, name=mangled_name)
        
        for i, param_name in enumerate(param_names):
            if isinstance(param_types[i], ir.PointerType) and isinstance(param_types[i].pointee, ir.ArrayType):# type: ignore
                self.env.define(param_name, func.args[i], param_types[i])
            else:
                ptr = self.builder.alloca(param_types[i], name=param_name)
                self.builder.store(func.args[i], ptr)
                self.env.define(param_name, ptr, param_types[i])

        self.compile(body)

        if self.builder.block is not None and not self.builder.block.is_terminated:
            if inferred_type == "void":
                self.builder.ret_void()

        self.builder = caller_builder
        self.env = caller_env
        self.is_in_main = was_in_main

        return func, return_ir_type
    
    def visit_reserve_call(self, node: ReserveCall) -> tuple[ir.Value, ir.Type] | None:
        size_result = self.resolve_value(node.size_expr)
        if size_result is None:
            self.report_error("Could not resolve size argument for reserve().")
            return None

        data_size_bytes, _ = size_result

        element_type = self.type_map['int']
        element_size_const = ir.Constant(ir.IntType(32), 4)  

        element_count = self.builder.sdiv(data_size_bytes, element_size_const, "elem_count")

        header_size = ir.Constant(ir.IntType(32), 4)
        total_size = self.builder.add(header_size, data_size_bytes, "total_array_size")

        malloc_func_res = self.env.lookup("reserve")
        if malloc_func_res is None:
            return self.report_error("Internal error: C function 'malloc' not found.")
        malloc_func, _ = malloc_func_res

        raw_ptr = self.builder.call(malloc_func, [total_size], name="raw_heap_ptr")

        len_ptr = self.builder.bitcast(raw_ptr, ir.IntType(32).as_pointer(), name="len_header_ptr")
        self.builder.store(element_count, len_ptr)

        data_ptr_i8 = self.builder.gep(raw_ptr, [header_size], inbounds=True, name="data_section_i8_ptr")

        typed_data_ptr = self.builder.bitcast(data_ptr_i8, ir.PointerType(element_type), "typed_data_ptr")
        if typed_data_ptr is None:
            self.report_error("Internal error: bitcast to typed pointer failed.")
            return None
        return typed_data_ptr, ir.PointerType(element_type)

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
            value = self.builder.icmp_signed('==', right_value, ir.Constant(ir.IntType(1), 0), name='not_res')
            Type = ir.IntType(1)
        if isinstance(right_type,ir.FloatType):
            Type=ir.FloatType()
            match operator:
                case '-':
                    value=self.builder.fmul(right_value,ir.Constant(ir.FloatType(),-1.0))
        elif isinstance(right_type, ir.DoubleType):
            Type=ir.DoubleType()
            match operator:
                case '-':
                    value=self.builder.fmul(right_value,ir.Constant(ir.DoubleType(),-1.0))
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
            case NodeType.AsExpression: 
                return self.visit_as_expression(cast(AsExpression, node))
            case NodeType.StructAccessExpression:
                return self.visit_member_access(cast(StructAccessExpression, node))
            
            case NodeType.MeasureExpression: 
                return self.visit_measure_expression(cast(MeasureExpression, node))
            
            case NodeType.SuperExpression:
                result = self.env.lookup("this")
                if result is None:
                    self.report_error("'super' can only be used inside a class method.")
                    return None
                return result[0], result[1]
            
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
            
            case NodeType.DoubleLiteral: 
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
                    this_entry = self.env.lookup("this")
                    if this_entry:
                        this_ptr, this_type = this_entry
                        class_type = this_type.pointee # type: ignore
                        class_name = class_type.name
                        layout = self.struct_layouts.get(class_name)
                        
                        if layout and ident_node.value in layout:
                            member_index = layout[ident_node.value]
                            zero = ir.Constant(ir.IntType(32), 0)
                            idx = ir.Constant(ir.IntType(32), member_index)
                            
                            member_ptr = self.builder.gep(this_ptr, [zero, idx], inbounds=True, name=f"{ident_node.value}_ptr")
                            loaded_val = self.builder.load(member_ptr, name=ident_node.value)
                            return loaded_val, loaded_val.type

                    self.report_error(f"Undefined variable '{ident_node.value}'")
                    return None

                ptr, typ = result

             
                if isinstance(typ, ir.PointerType) and (
                    isinstance(typ.pointee, ir.ArrayType) or # type: ignore
                    isinstance(typ.pointee, ir.IdentifiedStructType) # type: ignore
                ):
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
                string_global, _ = self.convert_string(str_node.value)
                string_ptr = self.builder.gep(string_global, 
                                              [ir.Constant(ir.IntType(32), 0), ir.Constant(ir.IntType(32), 0)], 
                                              inbounds=True)
                return string_ptr, ir.IntType(8).as_pointer()

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
                return self.input_string(scanf_func)

            case NodeType.CastExpression: 
                return self.visit_cast_expression(cast(CastExpression, node))


            case NodeType.CallExpression:
                if isinstance(node, CallExpression):
                    return self.visit_call_expression(node)
                else:
                    self.report_error("Expected CallExpression node, got something else.")
                    return None

    def input_float(self, scanf_func):
        format_string = "%f\0"
        c_fmt = ir.Constant(ir.ArrayType(ir.IntType(8), len(format_string)),
                            bytearray(format_string.encode("utf8")))
        global_fmt = ir.GlobalVariable(self.module, c_fmt.type,
                                    name=f"__scanf_float_format_{self.increment_counter()}")
        global_fmt.linkage = 'internal'
        global_fmt.global_constant = True
        global_fmt.initializer = c_fmt # type: ignore
        fmt_ptr = self.builder.bitcast(global_fmt, ir.IntType(8).as_pointer())

        float_ptr = self.builder.alloca(self.type_map['float'], name="input_float_ptr")
        self.builder.call(scanf_func, [fmt_ptr, float_ptr])
        loaded_value = self.builder.load(float_ptr, name="input_float_val")
        return loaded_value, self.type_map['float']

    
    def visit_cast_expression(self, node: CastExpression) -> Optional[tuple[ir.Value, ir.Type]]:
        target_type_str = node.target_type.value

        if node.expression.type() == NodeType.InputExpression:
            scanf_func_result = self.env.lookup("input")
            if scanf_func_result is None:
                self.report_error("Built-in function 'scanf' not found.")
                return None
            scanf_func, _ = scanf_func_result

            if target_type_str == "int":
                return self.input_int(scanf_func)
            elif target_type_str in ["float", "double"]:
                return self.input_float(scanf_func) 
            elif target_type_str == "str":
                return self.input_string(scanf_func)
            else:
                self.report_error(f"Cannot read input directly as type '{target_type_str}'.")
                return None

        val_res = self.resolve_value(node.expression)
        if val_res is None:
            self.report_error("Cannot resolve expression for casting.")
            return None
        
        original_val, original_type = val_res
        
        if target_type_str not in self.type_map:
            self.report_error(f"Unknown type '{target_type_str}' for casting.")
            return None
            
        target_type = self.type_map[target_type_str]

        if isinstance(original_type, ir.IntType) and isinstance(target_type, (ir.FloatType, ir.DoubleType)):
            cast_val = self.builder.sitofp(original_val, target_type)
            if cast_val is None:
                return None
            return cast_val, target_type
            
        if isinstance(original_type, (ir.FloatType, ir.DoubleType)) and isinstance(target_type, ir.IntType):
            cast_val = self.builder.fptosi(original_val, target_type)
            if cast_val is None:
                return None
            return cast_val, target_type
        
        if original_type == target_type:
            return original_val, original_type

        self.report_error(f"Unsupported cast from {original_type} to {target_type}.")
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
            malloc_func_result = self.env.lookup("reserve")
            if malloc_func_result is None:
                self.report_error("Built-in function 'reserve' (malloc) not found.")
                return None
            malloc_func, _ = malloc_func_result

            header_size = ir.Constant(ir.IntType(32), 4)
            raw_ptr = self.builder.call(malloc_func, [header_size], name="empty_array_ptr")

            len_ptr = self.builder.bitcast(raw_ptr, ir.IntType(32).as_pointer(), name="len_header_ptr")
            self.builder.store(ir.Constant(ir.IntType(32), 0), len_ptr)

            data_ptr_i8 = self.builder.gep(raw_ptr, [header_size], inbounds=True, name="data_section_i8_ptr")
            
            element_type = self.type_map['int']
            typed_data_ptr = self.builder.bitcast(data_ptr_i8, ir.PointerType(element_type), name="typed_data_ptr")
            if typed_data_ptr is None:
                self.report_error("Internal Error: Failed to create typed data pointer for empty array.")
                return None
            return typed_data_ptr, ir.PointerType(element_type)

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

        target_type = element_types[0]
        is_numeric = all(isinstance(t, (ir.IntType, ir.FloatType, ir.DoubleType)) for t in element_types)
        
        if is_numeric:
            if any(isinstance(t, ir.DoubleType) for t in element_types):
                target_type = self.type_map['double']
            elif any(isinstance(t, ir.FloatType) for t in element_types):
                target_type = self.type_map['float']
            else:
                target_type = self.type_map['int']
        else:
            if not all(t == target_type for t in element_types):
                self.report_error("All elements in a non-numeric array must have the same type.")
                return None

        promoted_values = []
        for val, current_type in zip(element_values, element_types):
            if current_type == target_type:
                promoted_values.append(val)
                continue
            
            promoted_val = None
            if isinstance(target_type, ir.DoubleType):
                if isinstance(current_type, ir.IntType):
                    promoted_val = self.builder.sitofp(val, target_type, name="i_to_d")
                elif isinstance(current_type, ir.FloatType):
                    promoted_val = self.builder.fpext(val, target_type, name="f_to_d")
            elif isinstance(target_type, ir.FloatType):
                if isinstance(current_type, ir.IntType):
                    promoted_val = self.builder.sitofp(val, target_type, name="i_to_f")
            
            if promoted_val is not None:
                promoted_values.append(promoted_val)
            else:
                self.report_error(f"Internal Error: Unhandled promotion from {current_type} to {target_type}")
                return None
        
        array_len = len(promoted_values)
        element_type = target_type
        
        if isinstance(target_type, str):
            if target_type not in self.type_map:
                self.report_error(f"Unknown type: {target_type}")
                return None
            target_type = self.type_map[target_type]

        
        if isinstance(element_type, ir.IntType):
            element_size_in_bytes = element_type.width // 8
        elif isinstance(element_type, ir.FloatType):
            element_size_in_bytes = 4
        elif isinstance(element_type, ir.DoubleType):
            element_size_in_bytes = 8
        else:
            
            element_size_in_bytes = 8

        data_size = self.builder.mul(
            ir.Constant(ir.IntType(32), element_size_in_bytes),
            ir.Constant(ir.IntType(32), array_len),
            name="data_size_bytes"
        )
        header_size = ir.Constant(ir.IntType(32), 4) 
        total_size = self.builder.add(header_size, data_size, name="total_array_size")

        malloc_func_result = self.env.lookup("reserve")
        if malloc_func_result is None:
            self.report_error("Built-in function 'reserve' (malloc) not found.")
            return None
        malloc_func, _ = malloc_func_result
        raw_ptr = self.builder.call(malloc_func, [total_size], name="raw_heap_ptr")

        len_ptr = self.builder.bitcast(raw_ptr, ir.IntType(32).as_pointer(), name="len_header_ptr")
        self.builder.store(ir.Constant(ir.IntType(32), array_len), len_ptr)

        data_ptr_i8 = self.builder.gep(raw_ptr, [header_size], inbounds=True, name="data_section_i8_ptr")
        data_ptr_typed = self.builder.bitcast(data_ptr_i8, ir.PointerType(element_type), name="typed_data_ptr")
        
        
        for idx, val in enumerate(promoted_values):
            element_ptr = self.builder.gep(
                data_ptr_typed,
                [ir.Constant(ir.IntType(32), idx)],
                inbounds=True
            )
            self.builder.store(val, element_ptr)
        
        
        if data_ptr_typed is None:
            self.report_error("Internal Error: Failed to create typed data pointer for array.")
            return None  
        return data_ptr_typed, ir.PointerType(element_type)

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

        if not isinstance(index_type, ir.IntType):
            self.report_error("Array index must be an integer.")
            return None

        if isinstance(array_type, ir.PointerType):
            
            elem_type = array_type.pointee # type: ignore
            
            element_ptr = self.builder.gep(
                array_val,
                [index_value],
                inbounds=True,
                name="array_element_ptr"
            )
        
        else:
            self.report_error(f"Cannot index into a non-pointer type. Got {array_type}")
            return None

        loaded_value = self.builder.load(element_ptr, name="array_element_value")
        return loaded_value, elem_type

    def convert_string(self,string:str)->tuple[ir.GlobalVariable, ir.Type]:
        string=string.replace("\\n","\n")
        fmt_with_null = f"{string}\0"
        
        fmt_bytes = bytearray(fmt_with_null.encode("utf8"))
        
        c_fmt = ir.Constant(ir.ArrayType(ir.IntType(8), len(fmt_bytes)), fmt_bytes)

        global_fmt = ir.GlobalVariable(self.module, c_fmt.type, name=f'__str_{self.increment_counter()}')
        global_fmt.linkage = 'internal'
        global_fmt.global_constant = True
        global_fmt.initializer = c_fmt # type: ignore
        return global_fmt, global_fmt.type

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
        
        member_types: list[ir.Type] = []
        member_layout: dict[str, int] = {}
        
        # handle inheritance
        parent_name = None
        if node.parent:
            parent_name = node.parent.value
            if parent_name is None or parent_name not in self.struct_types:
                return self.report_error(f"Parent class '{parent_name}' not found for class '{class_name}'.")
            
            self.class_parents[class_name] = parent_name
            parent_type = self.struct_types[parent_name]
            member_types.append(parent_type) 

            self.class_methods[class_name] = self.class_methods.get(parent_name, []).copy()
        else:
            self.class_methods[class_name] = []

        member_offset = len(member_types) 
        for i, member_var_stmt in enumerate(node.variables):
            member_name = cast(IdentifierLiteral, member_var_stmt.name).value
            if member_name is None:
                self.report_error(f"Invalid member in class '{class_name}'.")
                continue
            
            member_type_str = member_var_stmt.value_type if member_var_stmt.value_type else 'int'
            member_type = self.type_map.get(member_type_str, self.type_map['int'])
            member_types.append(member_type)
            member_layout[member_name] = i + member_offset
        
        self.struct_layouts[class_name] = member_layout
        class_type.set_body(*member_types)
        
        for method_node in node.methods:
            if method_node.name is None or method_node.name.value is None:
                self.report_error("Method in class has no name.")
                continue
            
            method_name = method_node.name.value
            if method_name not in self.class_methods[class_name]:
                 self.class_methods[class_name].append(method_name)

            num_params = len(method_node.parameters) if method_node.parameters else 0
            mangled_name = f"{class_name}_{method_name}_{num_params}"
            
            original_name = method_node.name.value
            method_node.name.value = mangled_name 
            self.compile_method_function(method_node, class_type)
            method_node.name.value = original_name


   
    def compile_method_function(self, node: FunctionStatement, class_type: ir.IdentifiedStructType) -> None:
        if node.name is None or node.name.value is None:
            raise ValueError("Method name is missing.")
        mangled_name: str = node.name.value

        params: list[FunctionParameter] = node.parameters or []
        param_names: list[str] = [p.name for p in params if p.name]
        param_types: list[ir.Type] = [self.type_map.get(p.value_type if p.value_type is not None else 'int', self.type_map['int']) for p in params]

       
        return_ir_type: ir.Type
        if node.return_type:
            return_ir_type = self.type_map.get(node.return_type, self.type_map['int'])
        else:
            previous_builder = self.builder
            previous_env = self.env

            dummy_module = ir.Module()
            dummy_func_type = ir.FunctionType(ir.VoidType(), [])
            dummy_func = ir.Function(dummy_module, dummy_func_type, "dummy_inference_func")
            dummy_block = dummy_func.append_basic_block("entry")
            self.builder = ir.IRBuilder(dummy_block)

            inference_env = Environment(parent=self.env)
            self.env = inference_env
            inference_env.define("this", ir.Constant(ir.PointerType(class_type), None), ir.PointerType(class_type))
            for i, param_name in enumerate(param_names):
                dummy_alloca = self.builder.alloca(param_types[i])
                inference_env.define(param_name, dummy_alloca, param_types[i])

            if node.body:
                self.compile(node.body)

            inferred_type = self._find_and_infer_return_type(node.body) if node.body else None
            return_ir_type = inferred_type if inferred_type is not None else self.type_map['void']

            self.builder = previous_builder
            self.env = previous_env
        
        this_param_type = ir.PointerType(class_type)
        final_param_types = [this_param_type] + param_types
        
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

        if self.builder.block is not None and not self.builder.block.is_terminated:
            if return_ir_type == ir.VoidType():
                self.builder.ret_void()
            else:
                self.builder.ret(ir.Constant(return_ir_type, 0))

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
            self.report_error("Member access '.' operator can only be used on class instances.")
            return None

        struct_type = cast(ir.IdentifiedStructType, obj_type.pointee) # type: ignore
        
        current_class_name = struct_type.name
        current_ptr = obj_ptr
        zero = ir.Constant(ir.IntType(32), 0)
        
        while current_class_name is not None:
            layout = self.struct_layouts.get(current_class_name)
            if layout and member_name in layout:
                member_index = layout[member_name]
                member_ptr = self.builder.gep(current_ptr, [zero, ir.Constant(ir.IntType(32), member_index)], inbounds=True, name=f"{member_name}_ptr")

                loaded_value = self.builder.load(member_ptr, name=member_name)
                return loaded_value, loaded_value.type

            parent_name = self.class_parents.get(current_class_name)
            if parent_name:
                current_ptr = self.builder.gep(current_ptr, [zero, zero], inbounds=True, name=f"{current_class_name}_to_{parent_name}_ptr")
            
            current_class_name = parent_name
            
        self.report_error(f"Class '{struct_type.name}' and its parents have no member named '{member_name}'.")
        return None
    
