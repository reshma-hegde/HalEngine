from abc import ABC, abstractmethod
from enum import Enum
from typing import List, Optional


class NodeType(Enum):
    Program = "Program"
    ExpressionStatement = "ExpressionStatement"
    InfixExpression = "InfixExpression"
    IntegerLiteral = "IntegerLiteral"
    FloatLiteral = "FloatLiteral"
    BooleanLiteral="BooleanLiteral"
    VarStatement="VarStatement"
    IdentifierLiteral="IdentifierLiteral"
    FunctionStatement="FunctionStatement"
    BlockStatement="BlockStatement"
    ReturnStatement="ReturnStatement"
    AssignStatement="AssignStatement"
    IfStatement="IfStatement"
    CallExpression="CallExpression"
    FunctionParameter="FunctionParameter"
    StringLiteral="StringLiteral"
    WhileStatement="WhileStatement"
    BreakStatement="BreakStatement"
    ConinueStatement="ContinueStatement"
    ForStatement="ForStatement"
    PrefixExpression="PrefixExpression"
    PostfixExpression="PostfixExpression"
    LoadStatement="LoadStatement"
    InputExpression = "InputExpression"
    ArrayLiteral="ArrayLiteral"
    ArrayAccessExpression="ArrayAccessExpression"
    NullLiteral = "NullLiteral"
    ReserveCall="ReserveCall"
    RefExpression="RefExpression"
    DerefExpression="DerefExpression"
    StructStatement = "StructStatement"
    MemberStatement = "MemberStatement"
    StructAccessExpression = "StructAccessExpression"
    StructInstanceExpression="StructInstanceExpression"
    ClassStatement = "ClassStatement"
    ThisExpression = "ThisExpression"
    RewindStatement = "RewindStatement"
    FastForwardStatement = "FastForwardStatement"
    BranchStatement = "BranchStatement"
    ForkStatement = "ForkStatement"
    QubitDeclarationStatement = "QubitDeclarationStatement"
    MeasureExpression = "MeasureExpression"
    QubitResetStatement = "QubitResetStatement"
    DoubleLiteral = "DoubleLiteral"
    SuperExpression = "SuperExpression"

    


class Node(ABC):
    @abstractmethod
    def type(self) -> NodeType:
        pass

    @abstractmethod
    def json(self) -> dict:
        pass


class Statement(Node):
    pass


class Expression(Node):
    pass


class Program(Node):
    def __init__(self) -> None:
        self.statements: list[Statement] = []

    def type(self) -> NodeType:
        return NodeType.Program

    def json(self) -> dict:
        return {
            "type": self.type().value,
            "statements": [{stmt.type().value: stmt.json()} for stmt in self.statements]
        }


class DoubleLiteral(Expression):
    def __init__(self, value: Optional[float] = None) -> None:
        self.value: Optional[float] = value

    def type(self) -> NodeType:
        return NodeType.DoubleLiteral

    def json(self) -> dict:
        return {
            "type": self.type().value,
            "value": self.value
        }

class MemberStatement(Statement):
    def __init__(self, name: 'IdentifierLiteral', value_type:Optional[str]) -> None:
        self.name = name
        self.value_type = value_type

    def type(self) -> NodeType:
        return NodeType.MemberStatement

    def json(self) -> dict:
        return {
            "type": self.type().value,
            "name": self.name.json(),
            "value_type": self.value_type
        }


class StructStatement(Statement):
    def __init__(self, name: 'IdentifierLiteral', members: List[MemberStatement]) -> None:
        self.name = name
        self.members = members

    def type(self) -> NodeType:
        return NodeType.StructStatement

    def json(self) -> dict:
        return {
            "type": self.type().value,
            "name": self.name.json(),
            "members": [member.json() for member in self.members]
        }


class StructInstanceExpression(Expression):
    def __init__(self, struct_name: 'IdentifierLiteral') -> None:
        self.struct_name = struct_name

    def type(self) -> NodeType:
        return NodeType.StructInstanceExpression

    def json(self) -> dict:
        return {
            "type": self.type().value,
            "struct_name": self.struct_name.json()
        }
        

class StructAccessExpression(Expression):
    def __init__(self, struct_name: Expression, member_name: 'IdentifierLiteral') -> None:
        self.struct_name = struct_name
        self.member_name = member_name
    
    def type(self) -> NodeType:
        return NodeType.StructAccessExpression
    
    def json(self) -> dict:
        return {
            "type": self.type().value,
            "struct_name": self.struct_name.json(),
            "member_name": self.member_name.json()
        }
    

class QubitDeclarationStatement(Statement):
    def __init__(self, name: 'IdentifierLiteral', initial_state: Optional['IntegerLiteral'] = None) -> None:
        self.name = name
        self.initial_state = initial_state

    def type(self) -> NodeType:
        return NodeType.QubitDeclarationStatement

    def json(self) -> dict:
        return {
            "type": self.type().value,
            "name": self.name.json(),
            "initial_state": self.initial_state.json() if self.initial_state else None
        }


class QubitResetStatement(Statement):
    def __init__(self, name: 'IdentifierLiteral', initial_state: Optional['IntegerLiteral'] = None) -> None:
        self.name = name
        self.initial_state = initial_state

    def type(self) -> NodeType:
        return NodeType.QubitResetStatement

    def json(self) -> dict:
        return {
            "type": self.type().value,
            "name": self.name.json(),
            "initial_state": self.initial_state.json() if self.initial_state else None
        }


class MeasureExpression(Expression):
    def __init__(self, target: 'IdentifierLiteral') -> None:

        self.target = target

    def type(self) -> NodeType:
        return NodeType.MeasureExpression

    def json(self) -> dict:
        return {
            "type": self.type().value,
            "target": self.target.json()
        }


class ForkStatement(Statement):
    def __init__(self, branches: List['BlockStatement'], merge_variable: 'IdentifierLiteral') -> None:
        self.branches = branches
        self.merge_variable = merge_variable

    def type(self) -> NodeType:
        return NodeType.ForkStatement

    def json(self) -> dict:
        return {
            "type": self.type().value,
            "branches": [branch.json() for branch in self.branches],
            "merge_variable": self.merge_variable.json()
        }


class BranchStatement(Statement):
    def __init__(self, try_block: 'BlockStatement', error_variable: 'IdentifierLiteral', handle_block: 'BlockStatement') -> None:
        self.try_block = try_block
        self.error_variable = error_variable
        self.handle_block = handle_block

    def type(self) -> NodeType:
        return NodeType.BranchStatement

    def json(self) -> dict:
        return {
            "type": self.type().value,
            "try_block": self.try_block.json(),
            "error_variable": self.error_variable.json(),
            "handle_block": self.handle_block.json()
        }


class RewindStatement(Statement):
    def __init__(self, steps: Expression) -> None:
        self.steps = steps

    def type(self) -> NodeType:
        return NodeType.RewindStatement

    def json(self) -> dict:
        return {
            "type": self.type().value,
            "steps": self.steps.json()
        }


class FastForwardStatement(Statement):
    def __init__(self, steps: Expression) -> None:
        self.steps = steps

    def type(self) -> NodeType:
        return NodeType.FastForwardStatement

    def json(self) -> dict:
        return {
            "type": self.type().value,
            "steps": self.steps.json()
        }


class FunctionParameter(Expression):
    def __init__(self,name:str,value_type: Optional[str]=None)->None:
        self.name=name
        self.value_type=value_type

    def type(self)->NodeType:
        return NodeType.FunctionParameter
    
    def json(self)->dict:
        return {
            "type":self.type().value,
            "name":self.name,
            "value_type":self.value_type
        }


class ExpressionStatement(Statement):
    def __init__(self, expr: Optional[Expression] = None) -> None:
        self.expr: Optional[Expression] = expr

    def type(self) -> NodeType:
        return NodeType.ExpressionStatement

    def json(self) -> dict:
        return {
            "type": self.type().value,
            "expr": self.expr.json() if self.expr else None
        }


class InputExpression(Expression):
    def __init__(self, value: str = "input") -> None:
        self.value = value

    def type(self) -> NodeType:
        return NodeType.InputExpression

    def json(self) -> dict:
        return {
            "type": self.type().value,
            "value": self.value
        }


class VarStatement(Statement):
    def __init__(self,name:Optional[Expression]=None,value:Optional[Expression]=None,value_type:Optional[str]=None)->None:
        self.name=name
        self.value=value
        self.value_type=value_type
    
    def type(self)->NodeType:
        return NodeType.VarStatement
    
    def json(self)->dict:
        return {
            "type" : self.type().value,
            "name":self.name.json() if  isinstance(self.name, Expression) else None,
            "value":self.value.json() if self.value else None,
            "value_type":self.value_type
        }
    

class ThisExpression(Expression):
    def type(self) -> NodeType:
        return NodeType.ThisExpression

    def json(self) -> dict:
        return {"type": self.type().value}
    

class SuperExpression(Expression):
    def type(self) -> NodeType:
        return NodeType.SuperExpression

    def json(self) -> dict:
        return {"type": self.type().value}
    

class ClassStatement(Statement):
    def __init__(self, name: 'IdentifierLiteral', parent: Optional['IdentifierLiteral'], variables: List['VarStatement'], methods: List['FunctionStatement']) -> None:
        self.name = name
        self.parent = parent
        self.variables = variables
        self.methods = methods

    def type(self) -> NodeType:
        return NodeType.ClassStatement
    
    def json(self) -> dict:
        return {
            "type": self.type().value,
            "name": self.name.json(),
            "parent": self.parent.json() if self.parent else None,
            "variables": [var.json() for var in self.variables],
            "methods": [method.json() for method in self.methods]
        }
    

class BlockStatement(Statement):
    def __init__(self,statements:list[Statement]| None = None)->None:
        self.statements=statements if statements is not None else[]
    
    def type(self)->NodeType:
        return NodeType.BlockStatement
    
    def json(self)->dict:
        return {
            "type":self.type().value,
            "statements":[stmt.json() for stmt in self.statements]
        }


class ReturnStatement(Statement):
    def __init__(self,return_value:Expression | None = None)->None:
        self.return_value=return_value

    def type(self)->NodeType:
        return NodeType.ReturnStatement
    
    def json(self)->dict:
        return {
            "type" :self.type().value,
            "return_value":self.return_value.json() if self.return_value is not None else None

        }


class FunctionStatement(Statement):
    def __init__(self,parameters: list[FunctionParameter] = [],body: Optional[BlockStatement] = None,name: Optional["IdentifierLiteral"] = None,return_type: Optional[str] = None) -> None:
        self.parameters=parameters
        self.body=body
        self.name=name
        self.return_type=return_type

    def type(self)->NodeType:
        return NodeType.FunctionStatement
    
    def json(self)->dict:
        return {
            "type":self.type().value,
            "name":self.name.json()if self.name is not None else None,
            "return_type":self.return_type,
            "parameters":[p.json() for p in self.parameters]if self.parameters is not None else [],
            "body":self.body.json() if self.body is not None else None,
        }


class AssignStatement(Statement):
    def __init__(self, ident: Optional[Expression] = None,operator:str="", right_value: Optional[Expression] = None) -> None:
        self.ident=ident
        self.operator=operator
        self.right_value=right_value

    def type(self)->NodeType:
        return NodeType.AssignStatement
    
    def json(self)->dict:
        return {
            "type":self.type().value,
            "ident":self.ident.json() if self.ident is not None else None,
            "right_value":self.right_value.json() if self.right_value is not None else None
        }


class IfStatement(Statement):
    def __init__(self,condition: Optional[Expression] = None,consequence: Optional[BlockStatement] = None,alternative: Optional[BlockStatement] = None,el_if: Optional['IfStatement'] = None) -> None:  
        self.condition = condition
        self.consequence = consequence
        self.alternative = alternative
        self.el_if = el_if 

    def type(self) -> NodeType:
        return NodeType.IfStatement

    def json(self) -> dict:
        return {
            "type": self.type().value,
            "condition": self.condition.json() if self.condition is not None else None,
            "consequence": self.consequence.json() if self.consequence is not None else None,
            "alternative": self.alternative.json() if self.alternative is not None else None,
            "el_if": self.el_if.json() if self.el_if is not None else None  # Added el_if
        }

class WhileStatement(Statement):
    def __init__(self,condition:Expression,body:Optional[BlockStatement]=None)->None:
        self.condition=condition
        self.body=body if body is not None else BlockStatement([])

    def type(self) -> NodeType:
        return NodeType.WhileStatement
    
    def json(self)->dict:
        return{
            "type":self.type().value,
            "condition":self.condition.json(),
            "body":self.body.json()
        }


class BreakStatement(Statement):
    def __init__(self)->None:
        pass
    def type(self)->NodeType:
        return NodeType.BreakStatement
    def json(self)->dict:
        return {
            "type":self.type().value
        }


class ContinueStatement(Statement):
    def __init__(self)->None:
        pass
    def type(self)->NodeType:
        return NodeType.ConinueStatement
    def json(self)->dict:
        return{
            "type":self.type().value
        }


class ForStatement(Statement):
    def __init__(self,var_declaration:Optional[VarStatement]=None,condition:Optional[Expression]=None,action:Optional[Expression]=None,body:Optional[BlockStatement]=None)->None:
        self.var_declaration=var_declaration
        self.condition=condition
        self.action=action
        self.body=body

    def type(self)->NodeType:
        return NodeType.ForStatement
    
    def json(self)->dict:
        return {
            "type":self.type().value,
            "var_decaration":self.var_declaration.json() if self.var_declaration is not None else None,
            "condition":self.condition.json() if self.condition is not None else None,
            "action":self.action.json() if self.action is not None else None,
            "body":self.body.json() if self.body is not None else None 
        }


class InfixExpression(Expression):
    def __init__(self, left_node: Expression, operator: str, right_node: Optional[Expression] = None) -> None:
        self.left_node: Expression = left_node
        self.operator: str = operator
        self.right_node: Optional[Expression] = right_node

    def type(self) -> NodeType:
        return NodeType.InfixExpression

    def json(self) -> dict:
        return {
            "type": self.type().value,
            "left_node": self.left_node.json(),
            "operator": self.operator,
            "right_node": self.right_node.json() if self.right_node else None
        }


class CallExpression(Expression):
    def __init__(self,function:Optional[Expression]=None,arguments:Optional[list[Expression]]=None)->None:
        self.function=function
        self.arguments=arguments

    def type(self)->NodeType:
        return NodeType.CallExpression
    def json(self)->dict:
        return {
            "type":self.type().value,
            "function":self.function.json() if self.function is not None else None,
            "arguments": [arg.json() for arg in self.arguments] if self.arguments is not None else None
        }


class PrefixExpression(Expression):
    def __init__(self,operator:str,right_node:Optional[Expression]=None)->None:
        self.operator=operator
        self.right_node=right_node

    def type(self)->NodeType:
        return NodeType.PrefixExpression
    
    def json(self)->dict:
        return {
            "type":self.type().value,
            "operator":self.operator,
            "right_node":self.right_node.json() if self.right_node is not None else None
        }


class PostfixExpression(Expression):
    def __init__(self,left_node:Expression,operator:str)->None:
        self.left_node=left_node
        self.operator=operator
    
    def type(self)->NodeType:
        return NodeType.PostfixExpression
    
    def json(self)->dict:
        return {
            "type":self.type().value,
            "left_node":self.left_node.json(),
            "operator":self.operator
        }


class LoadStatement(Statement):
    def __init__(self,file_path:str)->None:
        self.file_path=file_path

    def type(self)->NodeType:
        return NodeType.LoadStatement
    
    def json(self)->dict:
        return{
            "type":self.type().value,
            "file_path":self.file_path
        }


class IntegerLiteral(Expression):
    def __init__(self, value: Optional[int] = None) -> None:
        self.value: Optional[int] = value

    def type(self) -> NodeType:
        return NodeType.IntegerLiteral

    def json(self) -> dict:
        return {
            "type": self.type().value,
            "value": self.value
        }


class BooleanLiteral(Expression):
    def __init__(self, value: Optional[bool] = None) -> None:
        self.value: Optional[bool] = value

    def type(self) -> NodeType:
        return NodeType.BooleanLiteral

    def json(self) -> dict:
        return {
            "type": self.type().value,
            "value": self.value
        }


class FloatLiteral(Expression):
    def __init__(self, value: Optional[float] = None) -> None:
        self.value: Optional[float] = value

    def type(self) -> NodeType:
        return NodeType.FloatLiteral

    def json(self) -> dict:
        return {
            "type": self.type().value,
            "value": self.value
        }


class IdentifierLiteral(Expression):
    def __init__(self,value:Optional[str]=None) ->None:
        self.value: Optional[str]=value

    def type(self) -> NodeType:
        return NodeType.IdentifierLiteral

    def json(self) -> dict:
        return {
            "type": self.type().value,
            "value": self.value
        }


class StringLiteral(Expression):
    def __init__(self,value:Optional[str]=None)->None:
        self.value:Optional[str]=value

    def type(self) -> NodeType:
        return NodeType.StringLiteral

    def json(self) -> dict:
        return {
            "type": self.type().value,
            "value": self.value
        }


class ArrayLiteral(Expression):
    def __init__(self, elements: List[Expression]):
        self.elements = elements

    def type(self) -> NodeType:
        return NodeType.ArrayLiteral

    def json(self) -> dict:
        return {
            "type": self.type().value,
            "elements": [e.json() for e in self.elements]
        }


class NullLiteral(Expression):
    def __init__(self) -> None:
        self.value: None = None

    def type(self) -> NodeType:
        return NodeType.NullLiteral

    def json(self) -> dict:
        return {
            "type": self.type().value,
            "value": self.value
        }
    
    def __repr__(self) -> str:
        return f"NullLiteral(value={self.value})"


class ArrayAccessExpression(Expression):
    def __init__(self, array: Expression, index: Expression):
        self.array = array
        self.index = index

    def type(self) -> NodeType:
        return NodeType.ArrayAccessExpression

    def __repr__(self) -> str:
        return f"ArrayAccessExpression(array={self.array}, index={self.index})"

    def json(self) -> dict:
        return {
            "type": self.type().value,
            "array": self.array.json(),
            "index": self.index.json()
        }


class RefExpression(Expression):
    def __init__(self, expression_to_ref: Expression):
        self.expression_to_ref = expression_to_ref

    def type(self) -> NodeType:
        return NodeType.RefExpression

    def json(self) -> dict:
        return {
            "type": self.type().value,
            "expression_to_ref": self.expression_to_ref.json()
        }


class DerefExpression(Expression):
    def __init__(self, pointer_expression: Expression):
        self.pointer_expression = pointer_expression

    def type(self) -> NodeType:
        return NodeType.DerefExpression

    def json(self) -> dict:
        return {
            "type": self.type().value,
            "pointer_expression": self.pointer_expression.json()
        }


class ReserveCall(Expression):

    def __init__(self, size_expr: Expression):
        self.size_expr = size_expr
        self.ast_type = 'ReserveCall'
    
    def type(self) -> NodeType:
        return NodeType.ReserveCall
    
    def json(self) -> dict:
        return {
            "type": self.type().value,
            "size_expr": self.size_expr.json()
        }
    
