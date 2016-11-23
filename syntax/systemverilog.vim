if exists("b:current_syntax")
    if b:current_syntax == 'verilog'
        syntax clear
    else
        finish
    endif
endif

let b:current_syntax = "systemverilog"

set commentstring=//%s
set synmaxcol=1000

"-------------------------------------------------------------------------------
function! s:SynFunction(syn_type, group_name, list_to, link_to, ...)
    execute 'syntax '.a:syn_type.' '.a:group_name.' '.join(a:000, ' ')
    if a:list_to != 'NONE'
        execute 'syntax cluster '.a:list_to.' '.'add='.a:group_name
    endif
    if a:link_to != 'NONE'
        execute 'highlight default link '.a:group_name.' '.a:link_to
    endif
endfunction

command! -nargs=* Syn call s:SynFunction(<f-args>)

"-------------------------------------------------------------------------------

" object.item.field
" s     es   e
Syn match svItemParent NONE Type
    \ '\w\+\.'
    \ containedin=ALLBUT,@svContainsNone,svItemParent
    \ contains=NONE
    \ display

Syn region svPackedDimension svImplicitDataType NONE
    \ matchgroup=svParen
    \ start='\['
    \ end='\]'
    \ contains=svNumber
    \ containedin=svPortList,svItemParent
    \ transparent

syntax region svUnpackedDimension
    \ matchgroup=svParen
    \ start='\['
    \ end='\]'
    \ contains=svNumber
    \ transparent

syntax region svDataOrNetDeclaration
    \ start='\h\w*'
    \ end=';'me=s-1
    \ contains=svAssign,svNetType,svNonIntegerType,svIntegerAtomType,svIntegerVectorType,svSigning,svPackedDimension
    \ transparent
    \ nextgroup=svEndStatement
    \ skipwhite skipempty

Syn keyword svLifetime NONE Statement
    \ automatic static
    \ contained

Syn keyword svClassItemQualifier NONE Statement
    \ static protected local
    \ contained

Syn keyword svReturnWord NONE Keyword
    \ return
    \ contained containedin=svReturn

Syn region svReturn NONE NONE
    \ start="\<return\>"
    \ end=";"
    \ contains=svReturnWord
    \ contained
    \ containedin=@svSeqBodys

" TODO: Add parameters
Syn match svModuleInstance NONE NONE
    \ "\w\+\_s*\%(#(\_.\{-}\)\?\w\+\_s*(\_.\{-});"
    \ containedin=@svStaticSeqBodys

Syn match svVoid NONE svStatement
    \ "\<void'"
    \ containedin=@svSeqBodys
    \ nextgroup=svRParen
    \ skipwhite skipempty

Syn region svPortInstanceList NONE NONE
    \ start="("
    \ end=")"
    \ contains=svPortInstanceName
    \ contained
    \ containedin=svModuleInstance

Syn match svPortInstanceName NONE Special
    \ "\.\w\+"
    \ contained
    \ contains=NONE
    \ containedin=svPortInstanceList
    \ nextgroup=svRParen
    \ skipwhite skipempty

"-------------------------------------------------------------------------------
" Regions
"-------------------------------------------------------------------------------
let s:sv_region_map_array = [
    \ {'name'            : 'svModule',
    \  'start'           : 'module'  ,
    \  'end'             : 'endmodule',
    \  'keepend'         : 0,
    \  'header_contains' : [
    \      'svImport',
    \      'svParamDeclList',
    \      'svPortList'
    \    ],
    \  'body_contains'   : [
    \      '@svAlways'              ,
    \      '@svConcurrentAssertions',
    \      'svCase'                 ,
    \      'svClass'                ,
    \      'svClocking'             ,
    \      'svDataOrNetDeclaration' ,
    \      'svDefaultDisableIff'    ,
    \      'svFunction'             ,
    \      'svGenerate'             ,
    \      'svInterface'            ,
    \      'svModule'               ,
    \      'svPortList'             ,
    \      'svRParen'               ,
    \      'svSeqBlock'             ,
    \      'svStruct'               ,
    \      'svTask'                 ,
    \      'svTypedef'
    \    ],
    \  'containedin'     : ['svModuleBody', 'svInterfaceBody']
    \ },
    \ {'name'            : 'svInterface',
    \  'start'           : 'interface'  ,
    \  'end'             : 'endinterface',
    \  'keepend'         : 0,
    \  'header_contains' : [
    \      'svImport',
    \      'svParamDeclList',
    \      'svPortList'
    \    ],
    \  'body_contains'   : [
    \      '@svAlways'             ,
    \      'svCase'                ,
    \      'svClass'               ,
    \      'svClocking'            ,
    \      'svDataOrNetDeclaration',
    \      'svDefaultDisableIff' ,
    \      'svFunction'            ,
    \      'svInterface'           ,
    \      'svModule'              ,
    \      'svPortList'            ,
    \      'svSeqBlock'            ,
    \      'svStruct'              ,
    \      'svTask'                ,
    \      'svTypedef'
    \    ],
    \  'containedin'     : ['svModuleBody', 'svInterfaceBody']
    \ },
    \ {'name'            : 'svProgram',
    \  'start'           : 'program'  ,
    \  'end'             : 'endprogram',
    \  'keepend'         : 0,
    \  'header_contains' : ['svParamDeclList', 'svPortList'],
    \  'body_contains'   : [
    \      'svRParen'         ,
    \      'svTypedef'        ,
    \      'svStruct'        ,
    \      'svGenerate'       ,
    \      'svClass'          ,
    \      'svFunction'       ,
    \      'svTask'           ,
    \      'svSeqBlock'       ,
    \      'svCase'           ,
    \      'svDataOrNetDeclaration'
    \    ],
    \  'containedin'     : ['svProgramBody']
    \ },
    \ {'name'            : 'svFunction',
    \  'start'           : 'function'  ,
    \  'end'             : 'endfunction',
    \  'keepend'         : 1,
    \  'header_contains' : [
    \      'svLifetime',
    \      'svMethodName',
    \      'svArgs'
    \    ],
    \  'body_contains'   : [
    \      'svImmediateProperty',
    \      'svAssign',
    \      'svPortDeclaration',
    \      'svRParen',
    \      'svSeqBlock',
    \      'svDo',
    \      'svCase'
    \    ],
    \  'containedin'     : ['svClassBody', 'svModuleBody', 'svInterfaceBody']
    \ },
    \ {'name'            : 'svTask',
    \  'start'           : 'task'  ,
    \  'end'             : 'endtask',
    \  'keepend'         : 1,
    \  'header_contains' : ['svLifetime', 'svMethodName', 'svArgs'],
    \  'body_contains'   : [
    \      'svImmediateProperty',
    \      'svAssign',
    \      'svPortDeclaration',
    \      'svRParen',
    \      'svSeqBlock',
    \      'svDo'      ,
    \      'svCase'
    \    ],
    \  'containedin'     : ['svClassBody', 'svModuleBody', 'svInterfaceBody']
    \ },
    \ {'name'            : 'svInterfaceClass',
    \  'start'           : 'interface\s\+class'  ,
    \  'end'             : 'endclass',
    \  'keepend'         : 0,
    \  'body_contains'   : ['svPureDecl'],
    \  'containedin'     : ['svClassBody', 'svModuleBody', 'svInterfaceBody']
    \ },
    \ {'name'            : 'svClass',
    \  'start'           : 'class'  ,
    \  'end'             : 'endclass',
    \  'keepend'         : 0,
    \  'body_contains'   : [
    \      'svVirtual'   ,
    \      'svConstraint',
    \      'svExternDecl',
    \      'svPureDecl'  ,
    \      'svTypedef'   ,
    \      'svStruct'        ,
    \      'svClass'     ,
    \      'svFunction'  ,
    \      'svTask'
    \    ],
    \  'containedin'     : ['svClassBody', 'svModuleBody', 'svInterfaceBody']
    \ },
    \ {'name'            : 'svProperty',
    \  'start'           : 'property'  ,
    \  'end'             : 'endproperty',
    \  'keepend'         : 1,
    \  'body_contains'   : ['NONE'],
    \  'containedin'     : ['svModuleBody', 'svInterfaceBody', 'svClassBody']
    \ },
    \ {'name'            : 'svSequence',
    \  'start'           : 'sequence'  ,
    \  'end'             : 'endsequence',
    \  'keepend'         : 1,
    \  'body_contains'   : ['NONE'],
    \  'containedin'     : ['svModuleBody', 'svInterfaceBody', 'svClassBody']
    \ },
    \ {'name'            : 'svCovergroup',
    \  'start'           : 'covergroup'  ,
    \  'end'             : 'endgroup',
    \  'keepend'         : 1,
    \  'body_contains'   : ['svCoverpointWord'],
    \  'containedin'     : ['svModuleBody', 'svInterfaceBody', 'svClassBody']
    \ },
    \ {'name'            : 'svClocking',
    \  'start'           : '\%(default\s\+\)\?clocking'  ,
    \  'end'             : 'endclocking',
    \  'keepend'         : 1,
    \  'header_contains' : ['svSensitivityList'],
    \  'body_contains'   : ['NONE'],
    \  'containedin'     : ['svModuleBody', 'svInterfaceBody']
    \ },
    \ {'name'            : 'svPackage',
    \  'start'           : 'package'  ,
    \  'end'             : 'endpackage',
    \  'keepend'         : 1,
    \  'body_contains'   : [
    \      'svTypedef'        ,
    \      'svStruct'        ,
    \      'svModule', 'svInterface',
    \      'svClass', 'svFunction', 'svTask'
    \    ]
    \ }
    \ ]

for sv_region in s:sv_region_map_array
    let s:region_cmd =
        \ 'syntax region ' . sv_region.name .
        \ ' matchgroup=svRegion'.
        \ ' start="\<' . sv_region.start . '\>"' .
        \ ' end="\<' . sv_region.end . '\>"' .
        \ ' contains=' . sv_region.name . 'Header,' . sv_region.name . 'Body' .
        \ ' nextgroup=svEndLabel skipwhite' .
        \ ' transparent'

    let s:region_header_cmd =
        \ 'syntax region '. sv_region.name .'Header' .
        \ ' start="."' .
        \ ' end=";"me=s-1'.
        \ ' nextgroup=' . sv_region.name . 'Body' .
        \ ' contained'

    let s:region_body_cmd =
        \ 'syntax region ' . sv_region.name . 'Body' .
        \ ' start=";"rs=e+1' .
        \ ' end="\<' . sv_region.end .'\>"me=s-1' .
        \ ' contains=' . join(sv_region.body_contains, ',') .
        \ ' contained' .
        \ ' containedin=' . sv_region.name .
        \ ' transparent'

    if has_key(sv_region, 'header_contains')
        let s:region_header_cmd .=
            \ ' contains=' . join(sv_region.header_contains, ',')
    endif

    if has_key(sv_region, 'containedin')
        let s:region_cmd .=
            \ ' containedin='.join(sv_region.containedin, ',')
    endif

    if sv_region.keepend
        let s:region_cmd      .= ' keepend'
        let s:region_body_cmd .= ' keepend'
    endif
    "let s:region_cmd      .= ' fold'

    execute s:region_cmd
    execute s:region_header_cmd
    execute s:region_body_cmd
endfor

syntax cluster svSeqBodys
    \ contains=svFunctionBody,svTaskBody,svSeqBlock,svCase,svDo

syntax cluster svStaticSeqBodys
    \ contains=svModuleBody,svInterfaceBody,svStaticSeqBlock,svGenerate,svCase

Syn match svEndLabel NONE NONE
    \ ":\_s*\w\+"
    \ contains=NONE

"-------------------------------------------------------------------------------

Syn region svArgs NONE NONE
    \ matchgroup=svParen
    \ start="("
    \ end=")"
    \ contains=svArg
    \ contained

Syn match svArg NONE NONE
    \ ".\{-}\ze[,)]"
    \ contained
    \ containedin=svArgs

Syn region svParamAssign NONE NONE
    \ start="="
    \ end=";"
    \ contains=svOperator,svRParen,svUnpackedDimension,svNumber
    \ contained
    \ transparent
    \ keepend

Syn keyword svSigning svImplicitDataType Statement
    \ signed unsigned

Syn region svPortList NONE NONE
    \ matchgroup=svOperator
    \ start="("
    \ end=")"
    \ contains=svPortDeclaration
    \ contained containedin=svModule,svModuleBody,svInterface,svInterfaceBody
    \ transparent

Syn keyword svDefault NONE Keyword
    \ default
    \ contained

Syn keyword svPortDeclaration NONE Type
    \ input output inout
    \ contained containedin=svPortList

Syn keyword svNetType NONE Type
    \ supply0 supply1 tri triand trior trireg tri0 tri1 uwire wire wand wor
    \ containedin=svPortList
    \ nextgroup=svPackedDimension
    \ skipwhite skipempty

Syn keyword svNonIntegerType NONE Type
    \ shortreal real realtime

Syn keyword svIntegerAtomType NONE Type
    \ byte shortint int longint integer time
    \ nextgroup=svPackedDimension
    \ skipwhite skipempty

Syn keyword svIntegerVectorType NONE Type
    \ bit logic reg
    \ containedin=svPortList,svClassBody,svFunctionHeader,svFunctionBody,svTaskBody
    \ nextgroup=svPackedDimension
    \ skipwhite skipempty

Syn region svStatement NONE NONE
    \ start='[^ ]'
    \ end=';'
    \ contains=svAssign
    \ contained containedin=NONE
    \ transparent
    \ keepend

Syn match svEndStatement NONE svOperator
    \ ';'
    \ contains=NONE
    \ contained containedin=NONE

Syn match svIdentifier NONE NONE
    \ '\<\h\w*\>'
    \ contains=NONE
    \ contained containedin=NONE

Syn region svLocalParam NONE NONE
    \ matchgroup=svStatement
    \ start='localparam'
    \ end=';'he=s-1
    \ contains=@svImplicitDataType,svParamAssign
    \ containedin=@svStaticSeqBodys
    \ keepend

Syn match svMethodName NONE Function
    \ '\w\+\ze\_s*('
    \ contained

Syn region svDisable NONE NONE
    \ matchgroup=svStatement
    \ start='\<disable\>'
    \ end=';'he=s-1
    \ containedin=@svSeqBodys
    \ transparent
    \ keepend

Syn keyword svVirtual NONE Statement
    \ virtual
    \ nextgroup=svClass,svFunction,svTask

Syn match svIllegalIdentifier NONE Error
    \ "[^A-Za-z_ ]"
    \ contains=NONE
    \ contained
    \ containedin=svParam

"-------------------------------------------------------------------------------
" Let
"-------------------------------------------------------------------------------
Syn region svLetDeclaration NONE NONE
    \ start="\<let\>"
    \ end=";"me=s-1
    \ contains=svLetWord
    \ containedin=ALLBUT,@svContainsNone
    \ transparent

Syn keyword svLetWord NONE Statement
    \ let
    \ nextgroup=svLetIdentifier
    \ skipwhite skipempty

Syn match svLetIdentifier NONE NONE
    \ "\<\h\w*\>"
    \ contains=NONE
    \ contained
    \ containedin=NONE
    \ nextgroup=svLetPortList,svAssign
    \ skipwhite skipempty

Syn region svLetPortList NONE NONE
    \ matchgroup=svParen
    \ start="("
    \ end=")"
    \ contains=NONE
    \ contained
    \ containedin=NONE
    \ nextgroup=svLetPortList,svAssign
    \ skipwhite skipempty

"-------------------------------------------------------------------------------
" Parameters
"-------------------------------------------------------------------------------
"TODO: This section might be too strict.
"-------------------------------------------------------------------------------
Syn region svParamDeclList NONE NONE
    \ matchgroup=svOperator
    \ start="#("
    \ end=")"
    \ contains=svParam
    \ contained containedin=svModule
    \ transparent
    \ nextgroup=svPortList skipwhite skipempty

Syn match svParam NONE NONE
    \ "\h\_.\{-}\ze[,)]"
    \ contains=svParameterWord,svParamIdentifier,svIllegalIdentifier,svParamDefault
    \ contained
    \ containedin=svParamDeclList

Syn keyword svParameterWord NONE svStatement
    \ parameter
    \ contained
    \ containedin=svParam
    \ nextgroup=svParamIdentifier,svIllegalIdentifier
    \ skipwhite skipempty

Syn match svParamIdentifier NONE NONE
    \ "\<\h\w*\>"
    \ contains=NONE
    \ contained
    \ containedin=svParam
    \ nextgroup=svParamDefault
    \ skipwhite skipempty

Syn match svParamDefault NONE NONE
    \ "=[^,)]*"
    \ contains=svNumber,svOperator
    \ contained
    \ containedin=NONE

"-------------------------------------------------------------------------------
" Parenthesis
"-------------------------------------------------------------------------------
Syn region svRParen NONE NONE
    \ matchgroup=svParen
    \ start='('
    \ end=')'
    \ contains=svNumber,svRParen,svOperator
    \ transparent

Syn region svConcat NONE NONE
    \ matchgroup=svParen
    \ start='{'
    \ end='}'
    \ contains=svConcat,svNumber,svRParen,svPackedDimension
    \ transparent

Syn match svConcatDelimiter NONE svOperator
    \ ","
    \ contains=NONE
    \ containedin=svConcat

"-------------------------------------------------------------------------------
" Import
"-------------------------------------------------------------------------------
Syn region svImport NONE NONE
    \ start="\<import\>"
    \ end=";"
    \ contains=svImportWord
    \ contained
    \ nextgroup=svParamDeclList,svPortList
    \ skipwhite skipempty
    \ transparent
    \ keepend

Syn keyword svImportWord NONE svStatement
    \ import
    \ contained
    \ containedin=svImport

"-------------------------------------------------------------------------------
" Function/Task Declarations
"-------------------------------------------------------------------------------
"pure constraint Test;
"pure virtual function Test;
"pure virtual task Test;
Syn region svPureDecl NONE svStatement
    \ start="\<pure\%(\s\+virtual\)\>"
    \ end=";"he=s-1
    \ contains=svClassItemQualifier,svFunctionDecl,svTaskDecl

Syn region svExternDecl NONE svStatement
    \ start="\<extern\>"
    \ end=";"he=s-1
    \ contains=svPureDecl,svClassItemQualifier,svModuleDecl,svFunctionDecl,svTaskDecl

Syn region svModuleDecl NONE NONE
    \ matchgroup=svStatement
    \ start="\<module\>"
    \ end=";"me=s-1
    \ contains=svModuleHeader
    \ contained
    \ containedin=svExternDecl
    \ transparent

Syn region svFunctionDecl NONE NONE
    \ matchgroup=svStatement
    \ start="\<function\>"
    \ end=";"me=s-1
    \ contains=svFunctionHeader
    \ contained
    \ containedin=svPureDecl,svExternDecl
    \ transparent

Syn region svTaskDecl NONE NONE
    \ matchgroup=svStatement
    \ start="\<task\>"
    \ end=";"me=s-1
    \ contains=svTaskHeader
    \ contained
    \ containedin=svPureDecl,svExternDecl
    \ transparent

"-------------------------------------------------------------------------------
" Generate
"-------------------------------------------------------------------------------
Syn region svGenerate NONE NONE
    \ matchgroup=svRegion
    \ start="\<generate\>"
    \ end="\<endgenerate\>"
    \ contains=svStaticSeqBlock,@svAlways,svSensitivityList,svCond,@svConcurrentAssertions,svRParen
    \ containedin=svModuleBody,svInterfaceBody
    \ transparent
    \ keepend

"-------------------------------------------------------------------------------
" Numbers
"-------------------------------------------------------------------------------
syntax match svNumber "\<[0-9]\+\>"                       display
syntax match svNumber "'[01xX]\>"                         display
syntax match svNumber "[0-9]*'[sS]\?[bB][0-1_xX]\+"       display
syntax match svNumber "[0-9]*'[sS]\?[oO][0-7_xX]\+"       display
syntax match svNumber "[0-9]*'[sS]\?[dD][0-9_xX]\+"       display
syntax match svNumber "[0-9]*'[sS]\?[hH][0-9a-fA-F_xX]\+" display

highlight default link svNumber Number

"-------------------------------------------------------------------------------
" Assignments
"-------------------------------------------------------------------------------
Syn region svAssignStatement NONE NONE
    \ matchgroup=svStatement
    \ start='assign'
    \ end=';'he=s-1
    \ contains=svAssign
    \ containedin=@svStaticSeqBodys
    \ transparent
    \ keepend

Syn region svAssign NONE NONE
    \ matchgroup=svOperator
    \ start='[^=]\zs<\?=\ze[^=]\?'
    \ end=';'me=s-1
    \ contains=svNumber,svOperator,svRParen,svConcat,svConditionalAssign
    \ containedin=svAssignStatement
    \ transparent
    \ keepend

Syn match svConditionalAssign NONE svOperator
    \ '?\|:'
    \ contains=NONE
    \ containedin=svAssign
    \ display

"-------------------------------------------------------------------------------
" Do Statements
"-------------------------------------------------------------------------------
Syn region svDo NONE NONE
    \ matchgroup=svConditional
    \ start='\<do\>'
    \ end='\<while\>.*;'he=s+4
    \ contains=svRParen,svDefault,svSeqBlock,svAssign
    \ transparent

"-------------------------------------------------------------------------------
" Case Statements
"-------------------------------------------------------------------------------
"TODO: case () inside
"TODO: case labels/blocks

Syn region svCase NONE NONE
    \ matchgroup=svConditional
    \ start='\<case[zx]\?\>'
    \ end='\<endcase\>'
    \ contains=svCase,svDefault,svAssign,svPackedDimension,svNumber

Syn region svCaseParen NONE NONE
    \ matchgroup=svParen
    \ start='('
    \ end=')'
    \ contains=NONE
    \ contained containedin=svCase
    \ transparent
    \ nextgroup=svInside
    \ skipwhite skipempty

" Must be delcared after svCase
Syn keyword svInside NONE Keyword
    \ inside
    \ contained

"-------------------------------------------------------------------------------
" Sequential blocks (begin end)
"-------------------------------------------------------------------------------
Syn region svSeqBlock NONE NONE
    \ matchgroup=svRegion
    \ start="\<begin\>"
    \ end="\<end\>"
    \ contains=svAssign,svRParen,svSeqBlock,svCase,svDo
    \ containedin=@svSeqBodys
    \ transparent
    \ nextgroup=svEndLabel
    \ skipwhite skipempty

Syn region svStaticSeqBlock NONE NONE
    \ matchgroup=svRegion
    \ start="\<begin\>"
    \ end="\<end\>"
    \ contains=svCase,svDataOrNetDeclaration,@svAlways,svAssign,svRParen,
    \svAssignStatement,svStaticSeqBlock,@svConcurrentAssertions
    \ containedin=@svStaticSeqBodys
    \ transparent
    \ nextgroup=svEndLabel
    \ skipwhite skipempty

Syn match svSeqBlockLabel  NONE Label
    \ '\%(begin\s*:\s*\)\@<=\w\+'
    \ contained containedin=svSeqBlock,svStaticSeqBlock

Syn match svError NONE NONE
    \ "\s*\zs.*:\ze\s*end\>"
    \ contains=NONE
    \ containedin=svSeqBlock,svStaticSeqBlock
    \ display

"-------------------------------------------------------------------------------
" Fork Statements
"-------------------------------------------------------------------------------
Syn region svFork NONE NONE
    \ matchgroup=svRegion
    \ start="\<fork\>"
    \ end="\<join\%(_all\|_none\)\?\>"
    \ contains=svSeqBlock
    \ containedin=@svSeqBodys
    \ transparent

" Only procedural statements/blocks can be labelled.
Syn match svError NONE NONE
    \ "\s*\zs.*:\ze\s*join\%(_all\|_none\)\?\>"
    \ contains=NONE
    \ containedin=svFork
    \ display

Syn match svWaitFork NONE svStatement
    \ '\<wait\_s\+fork\_s*;'he=e-1
    \ contains=none
    \ containedin=@svSeqBodys

"-------------------------------------------------------------------------------
" Coverpoints
"-------------------------------------------------------------------------------
Syn keyword svCoverpointWord NONE svStatement
    \ coverpoint
    \ contained
    \ containedin=svCovergroupBody
    \ nextgroup=svCoverpointIdentifier
    \ skipwhite skipempty

Syn match svCoverpointIdentifier NONE NONE
    \ "\<\h\w*\>"
    \ contains=NONE
    \ contained
    \ containedin=NONE
    \ nextgroup=svCoverpointBins
    \ skipwhite skipempty

Syn region svCoverpointBins NONE NONE
    \ matchgroup=svParen
    \ start="{"
    \ end="}"
    \ contains=svCovergroupRangeList
    \ contained
    \ containedin=NONE

Syn region svCovergroupRangeList NONE NONE
    \ matchgroup=svParen
    \ start="{"
    \ end="}"
    \ contains=NONE
    \ contained
    \ containedin=NONE

"-------------------------------------------------------------------------------
" Typedef Statements
"-------------------------------------------------------------------------------
Syn keyword svStructWord NONE Typedef
    \ packed tagged
    \ containedin=svStruct

Syn region svTypedef  NONE NONE
    \ matchgroup=svType
    \ start='\<typedef\>'
    \ end=';'me=s-1
    \ contains=svUnion,svStruct

Syn region svUnion NONE NONE
    \ matchgroup=svType
    \ start='\<union\>'
    \ end=';'me=s-1
    \ contains=svTypeParen

Syn region svStruct NONE Structure
    \ matchgroup=svType
    \ start='\<struct\>'
    \ end=';'me=s-1
    \ contains=svTypeParen,svStructWord

Syn region svTypeParen NONE NONE
    \ matchgroup=svParen
    \ start='{'
    \ end='}'
    \ contains=svNumber,svRParen,svStruct
    \ transparent

"-------------------------------------------------------------------------------
" If Statement
"-------------------------------------------------------------------------------
" lewis6991 (10th Nov 16): After a LOT of experimentation with the syntax
" commands, I have come to the conclusion that it is impossible to define
" regions for 'if' and 'else' statements that would be consistent and useful.
" Therefore these statements will be treated independently to their conditional
" blocks. It is feasible for other conditional blocks as they don't have an
" 'else' but still quite difficult because comments can appear anywhere.
Syn keyword svCond NONE Conditional
    \ if forever repeat while foreach
    \ containedin=@svSeqBodys,@svStaticSeqBodys
    \ nextgroup=svStatementError,svRParen
    \ skipwhite skipempty

Syn keyword svFor NONE Conditional
    \ for
    \ containedin=@svSeqBodys
    \ nextgroup=svStatementError,svForParen
    \ skipwhite skipempty

Syn region svForParen NONE NONE
    \ matchgroup=svParen
    \ start='('
    \ end=')'
    \ contains=NONE
    \ contained
    \ containedin=NONE
    \ transparent

Syn keyword svLoopGenerateConstruct NONE Conditional
    \ for
    \ containedin=@svStaticSeqBodys,svModuleBody,svInterfaceBody
    \ nextgroup=svStatementError,svLoopGenerateConstructParen
    \ skipwhite skipempty

Syn region svLoopGenerateConstructParen NONE NONE
    \ matchgroup=svParen
    \ start='('
    \ end=')'
    \ contains=svAssign
    \ contained
    \ containedin=NONE
    \ transparent

Syn keyword svGenvar NONE Type
    \ genvar
    \ containedin=svLoopGenerateConstructParen
    \ nextgroup=svIdentifier
    \ skipwhite skipempty

Syn keyword svElse NONE Conditional
    \ else
    \ containedin=@svSeqBodys,@svStaticSeqBodys

Syn match svStatementError NONE svError
    \ '[^( ]\+'
    \ contains=NONE
    \ contained
    \ containedin=NONE
    \ display

"-------------------------------------------------------------------------------
" Always Statements
"-------------------------------------------------------------------------------
Syn keyword svAlwaysWord svAlways Statement
    \ always always_ff always_latch always_comb
    \ nextgroup=svAlwaysError2
    \ skipwhite skipempty

Syn match svSensitivityList svAlways NONE
    \ "@\s*\*"
    \ display

Syn region svSensitivityList NONE svOperator
    \ matchgroup=svParen
    \ start="@\_s*("
    \ end=")"
    \ contains=svSensitivityListWord
    \ transparent

Syn keyword svSensitivityListWord NONE Statement
    \ posedge negedge or
    \ contained
    \ containedin=svSensitivityList

" Only procedural statements/blocks can be labelled.
Syn match svAlwaysError svAlways svError
    \ ".*:\ze\s*always\%(_ff\|_latch\|_comb\)\?\>"
    \ contains=NONE

Syn match svAlwaysError2 NONE svError
    \ "\s*\zs:.*"
    \ contains=NONE
    \ contained containedin=NONE

"-------------------------------------------------------------------------------
" Constraints
"-------------------------------------------------------------------------------
Syn region svConstraintBody NONE NONE
    \ start="{"
    \ end="}"me=s-1
    \ transparent
    \ contained
    \ containedin=svConstraint

Syn region svConstraint NONE NONE
    \ matchgroup=svStatement
    \ start="constraint"
    \ end="}"he=s-1
    \ contains=svConstraintBody
    \ transparent

"-------------------------------------------------------------------------------
" Assertions
"-------------------------------------------------------------------------------
Syn match svAssertLabel NONE Label
    \ "[a-zA-Z_][a-zA-Z_0-9]*\s*:\ze\_s*\%(assert\|assume\|cover\)\>"
    \ nextgroup=svConcurrentProperty skipwhite skipempty

Syn keyword svAssertionKeyword NONE Statement
    \ assert assume cover property else
    \ contained
    \ containedin=svConcurrentProperty

Syn region svConcurrentProperty NONE NONE
    \ start="\<\%(assert\|assume\|cover\)\s\+property\_s*("
    \ end=";"
    \ contains=svAssertionKeyword,svPropertyParen
    \ transparent
    \ keepend

Syn region svPropertyParen NONE NONE
    \ matchgroup=svParen
    \ start='('
    \ end=')'
    \ contains=svImplication,svSensitivityList,svDisableIff,svRParen
    \ contained
    \ containedin=svConcurrentProperty
    \ transparent

Syn region svImplication NONE NONE
    \ start='|[-=]>'
    \ end=');'me=s-1
    \ contained
    \ contains=svRParen,svOperator
    \ containedin=svPropertyParen
    \ transparent

Syn cluster svConcurrentAssertions NONE NONE
    \ contains=svAssertLabel,svConcurrentProperty

Syn region svImmediateProperty NONE NONE
    \ start="\<\%(assert\|assume\|cover\)\_s*("
    \ end=";"
    \ contains=svAssertionKeyword,svRParen
    \ transparent

"-------------------------------------------------------------------------------
" Disable iff
"-------------------------------------------------------------------------------
Syn region svDefaultDisableIff NONE NONE
    \ matchgroup=svStatement
    \ start="\<\%(default\s*\)disable\s\+iff\s*\ze("
    \ end="\ze;"
    \ contains=svRParen
    \ containedin=svModuleBody,svInterface,svProperty,@svConcurrentAssertions
    \ keepend

Syn match svDisableIff NONE svStatement
    \ "\<disable\_s\+iff\>"
    \ nextgroup=svRParen
    \ skipwhite skipempty

"-------------------------------------------------------------------------------
" Attributes
"-------------------------------------------------------------------------------
Syn region svAttribute NONE Comment
    \ start="(\*"
    \ end="\*)"
    \ contains=NONE
    \ containedin=ALLBUT,@svContainsNone
    \ keepend

"-------------------------------------------------------------------------------
" System Tasks
"-------------------------------------------------------------------------------
Syn match svSystemTaskName NONE Define
    \ "$\w\+\>"
    \ contains=NONE
    \ contained
    \ containedin=svSystemTask
    \ display

Syn match svSystemTask NONE NONE
    \ "$\w\+\>(\_.\{-})"
    \ contains=svSystemTaskName,svRParen
    \ containedin=ALLBUT,@svContainsNone
    \ display

"-------------------------------------------------------------------------------
" Operator
"-------------------------------------------------------------------------------
Syn match svOperator NONE NONE
    \ "[~!|&/*=<>\[\]+\^\-]"
    \ contains=NONE
    \ display

"-------------------------------------------------------------------------------
" Preprocessor
"-------------------------------------------------------------------------------
Syn match svPreproc NONE Define
    \ "`[a-zA-Z_][a-zA-Z_0-9]*"
    \ contains=NONE
    \ containedin=ALLBUT,@svContainsNone
    "\ display "Cannot display

Syn match svIfdef NONE Define
    \ "`\(ifn\?def\|elsif\|undef\)"
    \ contains=NONE
    \ containedin=ALLBUT,@svContainsNone
    \ nextgroup=svPreprocIdentifier
    \ skipwhite skipempty

Syn match svPreprocIdentifier NONE NONE
    \ "\<\h\w*\>"
    \ contains=NONE
    \ contained
    \ containedin=NONE

"-------------------------------------------------------------------------------
" Defines
"-------------------------------------------------------------------------------
Syn match svDefineDeclaration svDefines Define
    \ "`define\>"
    \ contains=NONE
    \ containedin=svDefine
    \ nextgroup=svDefineIdentifier
    \ skipwhite skipempty

Syn match svDefineIdentifier svDefines Constant
    \ "\h\w*"
    \ contains=NONE
    \ contained containedin=NONE
    \ nextgroup=svDefineArgs,svDefineBody
    \ skipwhite skipempty
    \ display

Syn region svDefineBody svDefines NONE
    \ start="."
    \ skip="\\\\\n"
    \ end="\\n"
    \ contains=svDefineContinuation,svMacro
    \ contained containedin=NONE
    \ transparent
    \ keepend

Syn region svDefine svDefines NONE
    \ start="`define\>"
    \ skip="\\\\\n"
    \ end="\\n"
    \ contains=svDefineDeclaration
    \ containedin=ALLBUT,@svContainsNone
    \ transparent
    \ keepend

Syn match svDefineContinuation svDefines svOperator
    \ '\\\'
    \ contains=NONE
    \ contained containedin=svDefineBody

Syn region svDefineArgs svDefines NONE
    \ matchgroup=svParen
    \ start="("
    \ end=")"
    \ contains=svDefineArgsDelimiter
    \ contained containedin=NONE
    \ transparent
    \ nextgroup=svDefineBody
    \ skipwhite skipempty
    \ display

Syn match svDefineArgsDelimiter svDefines svOperator
    \ ","
    \ contains=NONE
    \ contained containedin=NONE
    \ display

"-------------------------------------------------------------------------------
Syn match svMacro NONE NONE
    \ "`\h\w*(\_.\{-})"
    \ contains=svPreproc,svRParen
    \ containedin=ALLBUT,@svContainsNone
    \ transparent
    \ display

Syn match svInclude NONE NONE
    \ "`include\>"
    \ contains=NONE
    \ containedin=ALLBUT,@svContainsNone
    \ nextgroup=svString
    \ skipwhite
    \ display

"-------------------------------------------------------------------------------
" String
"-------------------------------------------------------------------------------
Syn region svString NONE String
    \ start=+"+
    \ skip=+\\\"+
    \ end=+"+
    \ contains=@Spell
    \ containedin=ALLBUT,@svContainsNone
    \ keepend
    \ display

"-------------------------------------------------------------------------------
" Comments
"-------------------------------------------------------------------------------
Syn region svComment NONE Comment
    \ start="/\*"
    \ end="\*/"
    \ contains=@Spell
    \ containedin=ALLBUT,@svContainsNone
    \ keepend

Syn match svLineComment NONE Comment
    \ "//.*"
    \ contains=@Spell
    \ containedin=ALLBUT,@svContainsNone

"-------------------------------------------------------------------------------
syntax cluster svContainsNone
    \ contains=
    \svComment,
    \svLineComment,
    \@svDefines,
    \svString,
    \svAttribute,
    \svPreproc,
    \svMacro,
    \svSystemTask,
    \svSystemTaskName,
    \svEndLabel,
    \svIfdef,
    \svUndef

"-------------------------------------------------------------------------------
" Highlighting
"-------------------------------------------------------------------------------
highlight default link svConditional Conditional
highlight default link svError       Error
highlight default link svOperator    Special
highlight default link svParen       Special
highlight default link svRegion      Statement
highlight default link svStatement   Statement
highlight default link svType        Type

"-------------------------------------------------------------------------------
" Syncing
"-------------------------------------------------------------------------------

"syntax sync fromstart
syntax sync match svSync grouphere svModule    "extern\@<!\<module\>"
syntax sync match svSync grouphere svInterface "extern\@<!\<interface\>"
syntax sync match svSync grouphere svFunction  "extern\@<!\<function\>"
syntax sync match svSync grouphere svTask      "extern\@<!\<task\>"
syntax sync match svSync grouphere svClass     "extern\@<!\<class\>"
