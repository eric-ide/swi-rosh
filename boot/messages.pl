/*  Part of SWI-Rosh

    Author:        Jan Wielemaker
    E-mail:        J.Wielemaker@vu.nl
    WWW:           http://www.SWI-Rosh.org
    Copyright (c)  1997-2021, University of Amsterdam
                              VU University Amsterdam
                              CWI, Amsterdam
                              SWI-Rosh Solutions b.v.
    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:

    1. Redistributions of source code must retain the above copyright
       notice, this list of conditions and the following disclaimer.

    2. Redistributions in binary form must reproduce the above copyright
       notice, this list of conditions and the following disclaimer in
       the documentation and/or other materials provided with the
       distribution.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
    FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
    BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
    LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
    CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
    LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
    ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
    POSSIBILITY OF SUCH DAMAGE.
*/

:- module('$messages',
          [ print_message/2,            % +Kind, +Term
            print_message_lines/3,      % +Stream, +Prefix, +Lines
            message_to_string/2         % +Term, -String
          ]).

:- multifile
    prolog:message//1,              % entire message
    prolog:error_message//1,        % 1-st argument of error term
    prolog:message_context//1,      % Context of error messages
    prolog:deprecated//1,	    % Deprecated features
    prolog:message_location//1,     % (File) location of error messages
    prolog:message_line_element/2.  % Extend printing
:- '$hide'((
    prolog:message//1,
    prolog:error_message//1,
    prolog:message_context//1,
    prolog:deprecated//1,
    prolog:message_location//1,
    prolog:message_line_element/2)).

:- discontiguous
    prolog_message/3.

:- public
    translate_message//1.

:- create_prolog_flag(message_context, [thread], []).

%!  translate_message(+Term)// is det.
%
%   Translate a message Term into message lines. The produced lines
%   is a list of
%
%       * nl
%       Emit a newline
%       * Fmt-Args
%       Emit the result of format(Fmt, Args)
%       * Fmt
%       Emit the result of format(Fmt)
%       * flush
%       Used only as last element of the list.   Simply flush the
%       output instead of producing a final newline.
%       * at_same_line
%       Start the messages at the same line (instead of using ~N)

translate_message(Term) -->
    translate_message2(Term),
    !.
translate_message(Term) -->
    { Term = error(_, _) },
    [ 'Unknown exception: ~p'-[Term] ].
translate_message(Term) -->
    [ 'Unknown message: ~p'-[Term] ].

translate_message2(Term) -->
    {var(Term)},
    !,
    [ 'Unknown message: ~p'-[Term] ].
translate_message2(Term) -->
    prolog:message(Term).
translate_message2(Term) -->
    prolog_message(Term).
translate_message2(error(resource_error(stack), Context)) -->
    !,
    out_of_stack(Context).
translate_message2(error(resource_error(tripwire(Wire, Context)), _)) -->
    !,
    tripwire_message(Wire, Context).
translate_message2(error(existence_error(reset, Ball), SWI)) -->
    swi_location(SWI),
    tabling_existence_error(Ball, SWI).
translate_message2(error(ISO, SWI)) -->
    swi_location(SWI),
    term_message(ISO),
    swi_extra(SWI).
translate_message2('$aborted') -->
    [ 'Execution Aborted' ].
translate_message2(message_lines(Lines), L, T) :- % deal with old C-warning()
    make_message_lines(Lines, L, T).
translate_message2(format(Fmt, Args)) -->
    [ Fmt-Args ].

make_message_lines([], T, T) :- !.
make_message_lines([Last],  ['~w'-[Last]|T], T) :- !.
make_message_lines([L0|LT], ['~w'-[L0],nl|T0], T) :-
    make_message_lines(LT, T0, T).

term_message(Term) -->
    {var(Term)},
    !,
    [ 'Unknown error term: ~p'-[Term] ].
term_message(Term) -->
    prolog:error_message(Term).
term_message(Term) -->
    iso_message(Term).
term_message(Term) -->
    swi_message(Term).
term_message(Term) -->
    [ 'Unknown error term: ~p'-[Term] ].

iso_message(resource_error(Missing)) -->
    [ 'Not enough resources: ~w'-[Missing] ].
iso_message(type_error(evaluable, Actual)) -->
    { callable(Actual) },
    [ 'Arithmetic: `~p'' is not a function'-[Actual] ].
iso_message(type_error(free_of_attvar, Actual)) -->
    [ 'Type error: `~W'' contains attributed variables'-
      [Actual,[portray(true), attributes(portray)]] ].
iso_message(type_error(Expected, Actual)) -->
    [ 'Type error: `~w'' expected, found `~p'''-[Expected, Actual] ],
    type_error_comment(Expected, Actual).
iso_message(domain_error(Domain, Actual)) -->
    [ 'Domain error: '-[] ], domain(Domain),
    [ ' expected, found `~p'''-[Actual] ].
iso_message(instantiation_error) -->
    [ 'Arguments are not sufficiently instantiated' ].
iso_message(uninstantiation_error(Var)) -->
    [ 'Uninstantiated argument expected, found ~p'-[Var] ].
iso_message(representation_error(What)) -->
    [ 'Cannot represent due to `~w'''-[What] ].
iso_message(permission_error(Action, Type, Object)) -->
    permission_error(Action, Type, Object).
iso_message(evaluation_error(Which)) -->
    [ 'Arithmetic: evaluation error: `~p'''-[Which] ].
iso_message(existence_error(procedure, Proc)) -->
    [ 'Unknown procedure: ~q'-[Proc] ],
    unknown_proc_msg(Proc).
iso_message(existence_error(answer_variable, Var)) -->
    [ '$~w was not bound by a previous query'-[Var] ].
iso_message(existence_error(matching_rule, Goal)) -->
    [ 'No rule matches ~p'-[Goal] ].
iso_message(existence_error(Type, Object)) -->
    [ '~w `~p'' does not exist'-[Type, Object] ].
iso_message(existence_error(Type, Object, In)) --> % not ISO
    [ '~w `~p'' does not exist in ~p'-[Type, Object, In] ].
iso_message(busy(Type, Object)) -->
    [ '~w `~p'' is busy'-[Type, Object] ].
iso_message(syntax_error(swi_backslash_newline)) -->
    [ 'Deprecated ... \\<newline><white>*.  Use \\c' ].
iso_message(syntax_error(Id)) -->
    [ 'Syntax error: ' ],
    syntax_error(Id).
iso_message(occurs_check(Var, In)) -->
    [ 'Cannot unify ~p with ~p: would create an infinite tree'-[Var, In] ].

%!  permission_error(Action, Type, Object)//
%
%   Translate  permission  errors.  Most  follow    te  pattern  "No
%   permission to Action Type Object", but some are a bit different.

permission_error(Action, built_in_procedure, Pred) -->
    { user_predicate_indicator(Pred, PI)
    },
    [ 'No permission to ~w built-in predicate `~p'''-[Action, PI] ],
    (   {Action \== export}
    ->  [ nl,
          'Use :- redefine_system_predicate(+Head) if redefinition is intended'
        ]
    ;   []
    ).
permission_error(import_into(Dest), procedure, Pred) -->
    [ 'No permission to import ~p into ~w'-[Pred, Dest] ].
permission_error(Action, static_procedure, Proc) -->
    [ 'No permission to ~w static procedure `~p'''-[Action, Proc] ],
    defined_definition('Defined', Proc).
permission_error(input, stream, Stream) -->
    [ 'No permission to read from output stream `~p'''-[Stream] ].
permission_error(output, stream, Stream) -->
    [ 'No permission to write to input stream `~p'''-[Stream] ].
permission_error(input, text_stream, Stream) -->
    [ 'No permission to read bytes from TEXT stream `~p'''-[Stream] ].
permission_error(output, text_stream, Stream) -->
    [ 'No permission to write bytes to TEXT stream `~p'''-[Stream] ].
permission_error(input, binary_stream, Stream) -->
    [ 'No permission to read characters from binary stream `~p'''-[Stream] ].
permission_error(output, binary_stream, Stream) -->
    [ 'No permission to write characters to binary stream `~p'''-[Stream] ].
permission_error(open, source_sink, alias(Alias)) -->
    [ 'No permission to reuse alias "~p": already taken'-[Alias] ].
permission_error(tnot, non_tabled_procedure, Pred) -->
    [ 'The argument of tnot/1 is not tabled: ~p'-[Pred] ].
permission_error(Action, Type, Object) -->
    [ 'No permission to ~w ~w `~p'''-[Action, Type, Object] ].


unknown_proc_msg(_:(^)/2) -->
    !,
    unknown_proc_msg((^)/2).
unknown_proc_msg((^)/2) -->
    !,
    [nl, '  ^/2 can only appear as the 2nd argument of setof/3 and bagof/3'].
unknown_proc_msg((:-)/2) -->
    !,
    [nl, '  Rules must be loaded from a file'],
    faq('ToplevelMode').
unknown_proc_msg((=>)/2) -->
    !,
    [nl, '  Rules must be loaded from a file'],
    faq('ToplevelMode').
unknown_proc_msg((:-)/1) -->
    !,
    [nl, '  Directives must be loaded from a file'],
    faq('ToplevelMode').
unknown_proc_msg((?-)/1) -->
    !,
    [nl, '  ?- is the Prolog prompt'],
    faq('ToplevelMode').
unknown_proc_msg(Proc) -->
    { dwim_predicates(Proc, Dwims) },
    (   {Dwims \== []}
    ->  [nl, '  However, there are definitions for:', nl],
        dwim_message(Dwims)
    ;   []
    ).

dependency_error(shared(Shared), private(Private)) -->
    [ 'Shared table for ~p may not depend on private ~p'-[Shared, Private] ].
dependency_error(Dep, monotonic(On)) -->
    { '$pi_head'(PI, Dep),
      '$pi_head'(MPI, On)
    },
    [ 'Dependent ~p on monotonic predicate ~p is not monotonic or incremental'-
      [PI, MPI]
    ].

faq(Page) -->
    [nl, '  See FAQ at https://www.SWI-Rosh.org/FAQ/', Page, '.txt' ].

type_error_comment(_Expected, Actual) -->
    { type_of(Actual, Type),
      (   sub_atom(Type, 0, 1, _, First),
          memberchk(First, [a,e,i,o,u])
      ->  Article = an
      ;   Article = a
      )
    },
    [ ' (~w ~w)'-[Article, Type] ].

type_of(Term, Type) :-
    (   attvar(Term)      -> Type = attvar
    ;   var(Term)         -> Type = var
    ;   atom(Term)        -> Type = atom
    ;   integer(Term)     -> Type = integer
    ;   string(Term)      -> Type = string
    ;   Term == []        -> Type = empty_list
    ;   blob(Term, BlobT) -> blob_type(BlobT, Type)
    ;   rational(Term)    -> Type = rational
    ;   float(Term)       -> Type = float
    ;   is_stream(Term)   -> Type = stream
    ;   is_dict(Term)     -> Type = dict
    ;   is_list(Term)     -> Type = list
    ;   cyclic_term(Term) -> Type = cyclic
    ;   compound(Term)    -> Type = compound
    ;                        Type = unknown
    ).

blob_type(BlobT, Type) :-
    atom_concat(BlobT, '_reference', Type).

syntax_error(end_of_clause) -->
    [ 'Unexpected end of clause' ].
syntax_error(end_of_clause_expected) -->
    [ 'End of clause expected' ].
syntax_error(end_of_file) -->
    [ 'Unexpected end of file' ].
syntax_error(end_of_file_in_block_comment) -->
    [ 'End of file in /* ... */ comment' ].
syntax_error(end_of_file_in_quoted(Quote)) -->
    [ 'End of file in quoted ' ],
    quoted_type(Quote).
syntax_error(illegal_number) -->
    [ 'Illegal number' ].
syntax_error(long_atom) -->
    [ 'Atom too long (see style_check/1)' ].
syntax_error(long_string) -->
    [ 'String too long (see style_check/1)' ].
syntax_error(operator_clash) -->
    [ 'Operator priority clash' ].
syntax_error(operator_expected) -->
    [ 'Operator expected' ].
syntax_error(operator_balance) -->
    [ 'Unbalanced operator' ].
syntax_error(quoted_punctuation) -->
    [ 'Operand expected, unquoted comma or bar found' ].
syntax_error(list_rest) -->
    [ 'Unexpected comma or bar in rest of list' ].
syntax_error(cannot_start_term) -->
    [ 'Illegal start of term' ].
syntax_error(punct(Punct, End)) -->
    [ 'Unexpected `~w\' before `~w\''-[Punct, End] ].
syntax_error(undefined_char_escape(C)) -->
    [ 'Unknown character escape in quoted atom or string: `\\~w\''-[C] ].
syntax_error(void_not_allowed) -->
    [ 'Empty argument list "()"' ].
syntax_error(Message) -->
    [ '~w'-[Message] ].

quoted_type('\'') --> [atom].
quoted_type('\"') --> { current_prolog_flag(double_quotes, Type) }, [Type-[]].
quoted_type('\`') --> { current_prolog_flag(back_quotes, Type) }, [Type-[]].

domain(range(Low,High)) -->
    !,
    ['[~q..~q]'-[Low,High] ].
domain(Domain) -->
    ['`~w\''-[Domain] ].

%!  tabling_existence_error(+Ball, +Context)//
%
%   Called on invalid shift/1  calls.  Track   those  that  result  from
%   tabling errors.

tabling_existence_error(Ball, Context) -->
    { table_shift_ball(Ball) },
    [ 'Tabling dependency error' ],
    swi_extra(Context).

table_shift_ball(dependency(_Head)).
table_shift_ball(dependency(_Skeleton, _Trie, _Mono)).
table_shift_ball(call_info(_Skeleton, _Status)).
table_shift_ball(call_info(_GenSkeleton, _Skeleton, _Status)).

%!  dwim_predicates(+PI, -Dwims)
%
%   Find related predicate indicators.

dwim_predicates(Module:Name/_Arity, Dwims) :-
    !,
    findall(Dwim, dwim_predicate(Module:Name, Dwim), Dwims).
dwim_predicates(Name/_Arity, Dwims) :-
    findall(Dwim, dwim_predicate(user:Name, Dwim), Dwims).

dwim_message([]) --> [].
dwim_message([M:Head|T]) -->
    { hidden_module(M),
      !,
      functor(Head, Name, Arity)
    },
    [ '        ~q'-[Name/Arity], nl ],
    dwim_message(T).
dwim_message([Module:Head|T]) -->
    !,
    { functor(Head, Name, Arity)
    },
    [ '        ~q'-[Module:Name/Arity], nl],
    dwim_message(T).
dwim_message([Head|T]) -->
    {functor(Head, Name, Arity)},
    [ '        ~q'-[Name/Arity], nl],
    dwim_message(T).


swi_message(io_error(Op, Stream)) -->
    [ 'I/O error in ~w on stream ~p'-[Op, Stream] ].
swi_message(thread_error(TID, false)) -->
    [ 'Thread ~p died due to failure:'-[TID] ].
swi_message(thread_error(TID, exception(Error))) -->
    [ 'Thread ~p died abnormally:'-[TID], nl ],
    translate_message(Error).
swi_message(dependency_error(Tabled, DependsOn)) -->
    dependency_error(Tabled, DependsOn).
swi_message(shell(execute, Cmd)) -->
    [ 'Could not execute `~w'''-[Cmd] ].
swi_message(shell(signal(Sig), Cmd)) -->
    [ 'Caught signal ~d on `~w'''-[Sig, Cmd] ].
swi_message(format(Fmt, Args)) -->
    [ Fmt-Args ].
swi_message(signal(Name, Num)) -->
    [ 'Caught signal ~d (~w)'-[Num, Name] ].
swi_message(limit_exceeded(Limit, MaxVal)) -->
    [ 'Exceeded ~w limit (~w)'-[Limit, MaxVal] ].
swi_message(goal_failed(Goal)) -->
    [ 'goal unexpectedly failed: ~p'-[Goal] ].
swi_message(shared_object(_Action, Message)) --> % Message = dlerror()
    [ '~w'-[Message] ].
swi_message(system_error(Error)) -->
    [ 'error in system call: ~w'-[Error]
    ].
swi_message(system_error) -->
    [ 'error in system call'
    ].
swi_message(failure_error(Goal)) -->
    [ 'Goal failed: ~p'-[Goal] ].
swi_message(timeout_error(Op, Stream)) -->
    [ 'Timeout in ~w from ~p'-[Op, Stream] ].
swi_message(not_implemented(Type, What)) -->
    [ '~w `~p\' is not implemented in this version'-[Type, What] ].
swi_message(context_error(nodirective, Goal)) -->
    { goal_to_predicate_indicator(Goal, PI) },
    [ 'Wrong context: ~p can only be used in a directive'-[PI] ].
swi_message(context_error(edit, no_default_file)) -->
    (   { current_prolog_flag(windows, true) }
    ->  [ 'Edit/0 can only be used after opening a \c
               Prolog file by double-clicking it' ]
    ;   [ 'Edit/0 can only be used with the "-s file" commandline option'
        ]
    ),
    [ nl, 'Use "?- edit(Topic)." or "?- emacs."' ].
swi_message(context_error(function, meta_arg(S))) -->
    [ 'Functions are not (yet) supported for meta-arguments of type ~q'-[S] ].
swi_message(format_argument_type(Fmt, Arg)) -->
    [ 'Illegal argument to format sequence ~~~w: ~p'-[Fmt, Arg] ].
swi_message(format(Msg)) -->
    [ 'Format error: ~w'-[Msg] ].
swi_message(conditional_compilation_error(unterminated, Where)) -->
    [ 'Unterminated conditional compilation from '-[] ],
    cond_location(Where).
swi_message(conditional_compilation_error(no_if, What)) -->
    [ ':- ~w without :- if'-[What] ].
swi_message(duplicate_key(Key)) -->
    [ 'Duplicate key: ~p'-[Key] ].
swi_message(initialization_error(failed, Goal, File:Line)) -->
    !,
    [ '~w:~w: ~p: false'-[File, Line, Goal] ].
swi_message(initialization_error(Error, Goal, File:Line)) -->
    [ '~w:~w: ~p '-[File, Line, Goal] ],
    translate_message(Error).
swi_message(determinism_error(PI, det, Found, property)) -->
    (   { '$pi_head'(user:PI, Head),
          predicate_property(Head, det)
        }
    ->  [ 'Deterministic procedure ~p'-[PI] ]
    ;   [ 'Procedure ~p called from a deterministic procedure'-[PI] ]
    ),
    det_error(Found).
swi_message(determinism_error(PI, det, fail, guard)) -->
    [ 'Procedure ~p failed after $-guard'-[PI] ].
swi_message(determinism_error(PI, det, fail, guard_in_caller)) -->
    [ 'Procedure ~p failed after $-guard in caller'-[PI] ].
swi_message(determinism_error(Goal, det, fail, goal)) -->
    [ 'Goal ~p failed'-[Goal] ].
swi_message(determinism_error(Goal, det, nondet, goal)) -->
    [ 'Goal ~p succeeded with a choice point'-[Goal] ].
swi_message(qlf_format_error(File, Message)) -->
    [ '~w: Invalid QLF file: ~w'-[File, Message] ].
swi_message(goal_expansion_error(bound, Term)) -->
    [ 'Goal expansion bound a variable to ~p'-[Term] ].

det_error(nondet) -->
    [ ' succeeded with a choicepoint'- [] ].
det_error(fail) -->
    [ ' failed'- [] ].


cond_location(File:Line) -->
    { file_base_name(File, Base) },
    [ '~w:~d'-[Base, Line] ].

swi_location(X) -->
    { var(X)
    },
    !,
    [].
swi_location(Context) -->
    prolog:message_location(Context),
    !.
swi_location(context(Caller, _Msg)) -->
    { ground(Caller)
    },
    !,
    caller(Caller).
swi_location(file(Path, Line, -1, _CharNo)) -->
    !,
    [ '~w:~d: '-[Path, Line] ].
swi_location(file(Path, Line, LinePos, _CharNo)) -->
    [ '~w:~d:~d: '-[Path, Line, LinePos] ].
swi_location(stream(Stream, Line, LinePos, CharNo)) -->
    (   { is_stream(Stream),
          stream_property(Stream, file_name(File))
        }
    ->  swi_location(file(File, Line, LinePos, CharNo))
    ;   [ 'Stream ~w:~d:~d '-[Stream, Line, LinePos] ]
    ).
swi_location(autoload(File:Line)) -->
    [ '~w:~w: '-[File, Line] ].
swi_location(_) -->
    [].

caller(system:'$record_clause'/3) -->
    !,
    [].
caller(Module:Name/Arity) -->
    !,
    (   { \+ hidden_module(Module) }
    ->  [ '~q:~q/~w: '-[Module, Name, Arity] ]
    ;   [ '~q/~w: '-[Name, Arity] ]
    ).
caller(Name/Arity) -->
    [ '~q/~w: '-[Name, Arity] ].
caller(Caller) -->
    [ '~p: '-[Caller] ].


swi_extra(X) -->
    { var(X)
    },
    !,
    [].
swi_extra(Context) -->
    prolog:message_context(Context).
swi_extra(context(_, Msg)) -->
    { nonvar(Msg),
      Msg \== ''
    },
    !,
    swi_comment(Msg).
swi_extra(string(String, CharPos)) -->
    { sub_string(String, 0, CharPos, _, Before),
      sub_string(String, CharPos, _, 0, After)
    },
    [ nl, '~w'-[Before], nl, '** here **', nl, '~w'-[After] ].
swi_extra(_) -->
    [].

swi_comment(already_from(Module)) -->
    !,
    [ ' (already imported from ~q)'-[Module] ].
swi_comment(directory(_Dir)) -->
    !,
    [ ' (is a directory)' ].
swi_comment(not_a_directory(_Dir)) -->
    !,
    [ ' (is not a directory)' ].
swi_comment(Msg) -->
    [ ' (~w)'-[Msg] ].


thread_context -->
    { thread_self(Me), Me \== main, thread_property(Me, id(Id)) },
    !,
    ['[Thread ~w] '-[Id]].
thread_context -->
    [].

                 /*******************************
                 *        NORMAL MESSAGES       *
                 *******************************/

prolog_message(initialization_error(_, E, File:Line)) -->
    !,
    [ '~w:~d: '-[File, Line],
      'Initialization goal raised exception:', nl
    ],
    translate_message(E).
prolog_message(initialization_error(Goal, E, _)) -->
    [ 'Initialization goal ~p raised exception:'-[Goal], nl ],
    translate_message(E).
prolog_message(initialization_failure(_Goal, File:Line)) -->
    !,
    [ '~w:~d: '-[File, Line],
      'Initialization goal failed'-[]
    ].
prolog_message(initialization_failure(Goal, _)) -->
    [ 'Initialization goal failed: ~p'-[Goal]
    ].
prolog_message(initialization_exception(E)) -->
    [ 'Prolog initialisation failed:', nl ],
    translate_message(E).
prolog_message(init_goal_syntax(Error, Text)) -->
    !,
    [ '-g ~w: '-[Text] ],
    translate_message(Error).
prolog_message(init_goal_failed(failed, @(Goal,File:Line))) -->
    !,
    [ '~w:~w: ~p: false'-[File, Line, Goal] ].
prolog_message(init_goal_failed(Error, @(Goal,File:Line))) -->
    !,
    [ '~w:~w: ~p '-[File, Line, Goal] ],
    translate_message(Error).
prolog_message(init_goal_failed(failed, Text)) -->
    !,
    [ '-g ~w: false'-[Text] ].
prolog_message(init_goal_failed(Error, Text)) -->
    !,
    [ '-g ~w: '-[Text] ],
    translate_message(Error).
prolog_message(unhandled_exception(E)) -->
    [ 'Unhandled exception: ' ],
    (   translate_message2(E)
    ->  []
    ;   [ '~p'-[E] ]
    ).
prolog_message(goal_failed(Context, Goal)) -->
    [ 'Goal (~w) failed: ~p'-[Context, Goal] ].
prolog_message(no_current_module(Module)) -->
    [ '~w is not a current module (created)'-[Module] ].
prolog_message(commandline_arg_type(Flag, Arg)) -->
    [ 'Bad argument to commandline option -~w: ~w'-[Flag, Arg] ].
prolog_message(missing_feature(Name)) -->
    [ 'This version of SWI-Rosh does not support ~w'-[Name] ].
prolog_message(singletons(_Term, List)) -->
    [ 'Singleton variables: ~w'-[List] ].
prolog_message(multitons(_Term, List)) -->
    [ 'Singleton-marked variables appearing more than once: ~w'-[List] ].
prolog_message(profile_no_cpu_time) -->
    [ 'No CPU-time info.  Check the SWI-Rosh manual for details' ].
prolog_message(non_ascii(Text, Type)) -->
    [ 'Unquoted ~w with non-portable characters: ~w'-[Type, Text] ].
prolog_message(io_warning(Stream, Message)) -->
    { stream_property(Stream, position(Position)),
      !,
      stream_position_data(line_count, Position, LineNo),
      stream_position_data(line_position, Position, LinePos),
      (   stream_property(Stream, file_name(File))
      ->  Obj = File
      ;   Obj = Stream
      )
    },
    [ '~p:~d:~d: ~w'-[Obj, LineNo, LinePos, Message] ].
prolog_message(io_warning(Stream, Message)) -->
    [ 'stream ~p: ~w'-[Stream, Message] ].
prolog_message(option_usage(pldoc)) -->
    [ 'Usage: --pldoc[=port]' ].
prolog_message(interrupt(begin)) -->
    [ 'Action (h for help) ? ', flush ].
prolog_message(interrupt(end)) -->
    [ 'continue' ].
prolog_message(interrupt(trace)) -->
    [ 'continue (trace mode)' ].
prolog_message(unknown_in_module_user) -->
    [ 'Using a non-error value for unknown in the global module', nl,
      'causes most of the development environment to stop working.', nl,
      'Please use :- dynamic or limit usage of unknown to a module.', nl,
      'See https://www.SWI-Rosh.org/howto/database.html'
    ].
prolog_message(deprecated(What)) -->
    deprecated(What).
prolog_message(untable(PI)) -->
    [ 'Reconsult: removed tabling for ~p'-[PI] ].


                 /*******************************
                 *         LOADING FILES        *
                 *******************************/

prolog_message(modify_active_procedure(Who, What)) -->
    [ '~p: modified active procedure ~p'-[Who, What] ].
prolog_message(load_file(failed(user:File))) -->
    [ 'Failed to load ~p'-[File] ].
prolog_message(load_file(failed(Module:File))) -->
    [ 'Failed to load ~p into module ~p'-[File, Module] ].
prolog_message(load_file(failed(File))) -->
    [ 'Failed to load ~p'-[File] ].
prolog_message(mixed_directive(Goal)) -->
    [ 'Cannot pre-compile mixed load/call directive: ~p'-[Goal] ].
prolog_message(cannot_redefine_comma) -->
    [ 'Full stop in clause-body?  Cannot redefine ,/2' ].
prolog_message(illegal_autoload_index(Dir, Term)) -->
    [ 'Illegal term in INDEX file of directory ~w: ~w'-[Dir, Term] ].
prolog_message(redefined_procedure(Type, Proc)) -->
    [ 'Redefined ~w procedure ~p'-[Type, Proc] ],
    defined_definition('Previously defined', Proc).
prolog_message(declare_module(Module, abolish(Predicates))) -->
    [ 'Loading module ~w abolished: ~p'-[Module, Predicates] ].
prolog_message(import_private(Module, Private)) -->
    [ 'import/1: ~p is not exported (still imported into ~q)'-
      [Private, Module]
    ].
prolog_message(ignored_weak_import(Into, From:PI)) -->
    [ 'Local definition of ~p overrides weak import from ~q'-
      [Into:PI, From]
    ].
prolog_message(undefined_export(Module, PI)) -->
    [ 'Exported procedure ~q:~q is not defined'-[Module, PI] ].
prolog_message(no_exported_op(Module, Op)) -->
    [ 'Operator ~q:~q is not exported (still defined)'-[Module, Op] ].
prolog_message(discontiguous((-)/2,_)) -->
    prolog_message(minus_in_identifier).
prolog_message(discontiguous(Proc,Current)) -->
    [ 'Clauses of ', ansi(code, '~p', [Proc]),
      ' are not together in the source-file', nl ],
    current_definition(Proc, 'Earlier definition at '),
    [ 'Current predicate: ', ansi(code, '~p', [Current]), nl,
      'Use ', ansi(code, ':- discontiguous ~p.', [Proc]),
      ' to suppress this message'
    ].
prolog_message(decl_no_effect(Goal)) -->
    [ 'Deprecated declaration has no effect: ~p'-[Goal] ].
prolog_message(load_file(start(Level, File))) -->
    [ '~|~t~*+Loading '-[Level] ],
    load_file(File),
    [ ' ...' ].
prolog_message(include_file(start(Level, File))) -->
    [ '~|~t~*+include '-[Level] ],
    load_file(File),
    [ ' ...' ].
prolog_message(include_file(done(Level, File))) -->
    [ '~|~t~*+included '-[Level] ],
    load_file(File).
prolog_message(load_file(done(Level, File, Action, Module, Time, Clauses))) -->
    [ '~|~t~*+'-[Level] ],
    load_file(File),
    [ ' ~w'-[Action] ],
    load_module(Module),
    [ ' ~2f sec, ~D clauses'-[Time, Clauses] ].
prolog_message(dwim_undefined(Goal, Alternatives)) -->
    { goal_to_predicate_indicator(Goal, Pred)
    },
    [ 'Unknown procedure: ~q'-[Pred], nl,
      '    However, there are definitions for:', nl
    ],
    dwim_message(Alternatives).
prolog_message(dwim_correct(Into)) -->
    [ 'Correct to: ~q? '-[Into], flush ].
prolog_message(error(loop_error(Spec), file_search(Used))) -->
    [ 'File search: too many levels of indirections on: ~p'-[Spec], nl,
      '    Used alias expansions:', nl
    ],
    used_search(Used).
prolog_message(minus_in_identifier) -->
    [ 'The "-" character should not be used to separate words in an', nl,
      'identifier.  Check the SWI-Rosh FAQ for details.'
    ].
prolog_message(qlf(removed_after_error(File))) -->
    [ 'Removed incomplete QLF file ~w'-[File] ].
prolog_message(qlf(recompile(Spec,_Pl,_Qlf,Reason))) -->
    [ '~p: recompiling QLF file'-[Spec] ],
    qlf_recompile_reason(Reason).
prolog_message(qlf(can_not_recompile(Spec,QlfFile,_Reason))) -->
    [ '~p: can not recompile "~w" (access denied)'-[Spec, QlfFile], nl,
      '\tLoading from source'-[]
    ].
prolog_message(qlf(system_lib_out_of_date(Spec,QlfFile))) -->
    [ '~p: can not recompile "~w" (access denied)'-[Spec, QlfFile], nl,
      '\tLoading QlfFile'-[]
    ].
prolog_message(redefine_module(Module, OldFile, File)) -->
    [ 'Module "~q" already loaded from ~w.'-[Module, OldFile], nl,
      'Wipe and reload from ~w? '-[File], flush
    ].
prolog_message(redefine_module_reply) -->
    [ 'Please answer y(es), n(o) or a(bort)' ].
prolog_message(reloaded_in_module(Absolute, OldContext, LM)) -->
    [ '~w was previously loaded in module ~w'-[Absolute, OldContext], nl,
      '\tnow it is reloaded into module ~w'-[LM] ].
prolog_message(expected_layout(Expected, Pos)) -->
    [ 'Layout data: expected ~w, found: ~p'-[Expected, Pos] ].

defined_definition(Message, Spec) -->
    { strip_module(user:Spec, M, Name/Arity),
      functor(Head, Name, Arity),
      predicate_property(M:Head, file(File)),
      predicate_property(M:Head, line_count(Line))
    },
    !,
    [ nl, '~w at ~w:~d'-[Message, File,Line] ].
defined_definition(_, _) --> [].

used_search([]) -->
    [].
used_search([Alias=Expanded|T]) -->
    [ '        file_search_path(~p, ~p)'-[Alias, Expanded], nl ],
    used_search(T).

load_file(file(Spec, _Path)) -->
    (   {atomic(Spec)}
    ->  [ '~w'-[Spec] ]
    ;   [ '~p'-[Spec] ]
    ).
%load_file(file(_, Path)) -->
%       [ '~w'-[Path] ].

load_module(user) --> !.
load_module(system) --> !.
load_module(Module) -->
    [ ' into ~w'-[Module] ].

goal_to_predicate_indicator(Goal, PI) :-
    strip_module(Goal, Module, Head),
    callable_name_arity(Head, Name, Arity),
    user_predicate_indicator(Module:Name/Arity, PI).

callable_name_arity(Goal, Name, Arity) :-
    compound(Goal),
    !,
    compound_name_arity(Goal, Name, Arity).
callable_name_arity(Goal, Goal, 0) :-
    atom(Goal).

user_predicate_indicator(Module:PI, PI) :-
    hidden_module(Module),
    !.
user_predicate_indicator(PI, PI).

hidden_module(user) :- !.
hidden_module(system) :- !.
hidden_module(M) :-
    sub_atom(M, 0, _, _, $).

current_definition(Proc, Prefix) -->
    { pi_uhead(Proc, Head),
      predicate_property(Head, file(File)),
      predicate_property(Head, line_count(Line))
    },
    [ '~w~w:~d'-[Prefix,File,Line], nl ].
current_definition(_, _) --> [].

pi_uhead(Module:Name/Arity, Module:Head) :-
    !,
    atom(Module), atom(Name), integer(Arity),
    functor(Head, Name, Arity).
pi_uhead(Name/Arity, user:Head) :-
    atom(Name), integer(Arity),
    functor(Head, Name, Arity).

qlf_recompile_reason(old) -->
    !,
    [ ' (out of date)'-[] ].
qlf_recompile_reason(_) -->
    [ ' (incompatible with current Prolog version)'-[] ].

prolog_message(file_search(cache(Spec, _Cond), Path)) -->
    [ 'File search: ~p --> ~p (cache)'-[Spec, Path] ].
prolog_message(file_search(found(Spec, Cond), Path)) -->
    [ 'File search: ~p --> ~p OK ~p'-[Spec, Path, Cond] ].
prolog_message(file_search(tried(Spec, Cond), Path)) -->
    [ 'File search: ~p --> ~p NO ~p'-[Spec, Path, Cond] ].

                 /*******************************
                 *              GC              *
                 *******************************/

prolog_message(agc(start)) -->
    thread_context,
    [ 'AGC: ', flush ].
prolog_message(agc(done(Collected, Remaining, Time))) -->
    [ at_same_line,
      'reclaimed ~D atoms in ~3f sec. (remaining: ~D)'-
      [Collected, Time, Remaining]
    ].
prolog_message(cgc(start)) -->
    thread_context,
    [ 'CGC: ', flush ].
prolog_message(cgc(done(CollectedClauses, _CollectedBytes,
                        RemainingBytes, Time))) -->
    [ at_same_line,
      'reclaimed ~D clauses in ~3f sec. (pending: ~D bytes)'-
      [CollectedClauses, Time, RemainingBytes]
    ].

		 /*******************************
		 *        STACK OVERFLOW	*
		 *******************************/

out_of_stack(Context) -->
    { human_stack_size(Context.localused,   Local),
      human_stack_size(Context.globalused,  Global),
      human_stack_size(Context.trailused,   Trail),
      human_stack_size(Context.stack_limit, Limit),
      LCO is (100*(Context.depth - Context.environments))/Context.depth
    },
    [ 'Stack limit (~s) exceeded'-[Limit], nl,
      '  Stack sizes: local: ~s, global: ~s, trail: ~s'-[Local,Global,Trail], nl,
      '  Stack depth: ~D, last-call: ~0f%, Choice points: ~D'-
         [Context.depth, LCO, Context.choicepoints], nl
    ],
    overflow_reason(Context, Resolve),
    resolve_overflow(Resolve).

human_stack_size(Size, String) :-
    Size < 100,
    format(string(String), '~dKb', [Size]).
human_stack_size(Size, String) :-
    Size < 100 000,
    Value is Size / 1024,
    format(string(String), '~1fMb', [Value]).
human_stack_size(Size, String) :-
    Value is Size / (1024*1024),
    format(string(String), '~1fGb', [Value]).

overflow_reason(Context, fix) -->
    show_non_termination(Context),
    !.
overflow_reason(Context, enlarge) -->
    { Stack = Context.get(stack) },
    !,
    [ '  In:'-[], nl ],
    stack(Stack).
overflow_reason(_Context, enlarge) -->
    [ '  Insufficient global stack'-[] ].

show_non_termination(Context) -->
    (   { Stack = Context.get(cycle) }
    ->  [ '  Probable infinite recursion (cycle):'-[], nl ]
    ;   { Stack = Context.get(non_terminating) }
    ->  [ '  Possible non-terminating recursion:'-[], nl ]
    ),
    stack(Stack).

stack([]) --> [].
stack([frame(Depth, M:Goal, _)|T]) -->
    [ '    [~D] ~q:'-[Depth, M] ],
    stack_goal(Goal),
    [ nl ],
    stack(T).

stack_goal(Goal) -->
    { compound(Goal),
      !,
      compound_name_arity(Goal, Name, Arity)
    },
    [ '~q('-[Name] ],
    stack_goal_args(1, Arity, Goal),
    [ ')'-[] ].
stack_goal(Goal) -->
    [ '~q'-[Goal] ].

stack_goal_args(I, Arity, Goal) -->
    { I =< Arity,
      !,
      arg(I, Goal, A),
      I2 is I + 1
    },
    stack_goal_arg(A),
    (   { I2 =< Arity }
    ->  [ ', '-[] ],
        stack_goal_args(I2, Arity, Goal)
    ;   []
    ).
stack_goal_args(_, _, _) -->
    [].

stack_goal_arg(A) -->
    { nonvar(A),
      A = [Len|T],
      !
    },
    (   {Len == cyclic_term}
    ->  [ '[cyclic list]'-[] ]
    ;   {T == []}
    ->  [ '[length:~D]'-[Len] ]
    ;   [ '[length:~D|~p]'-[Len, T] ]
    ).
stack_goal_arg(A) -->
    { nonvar(A),
      A = _/_,
      !
    },
    [ '<compound ~p>'-[A] ].
stack_goal_arg(A) -->
    [ '~p'-[A] ].

resolve_overflow(fix) -->
    [].
resolve_overflow(enlarge) -->
    { current_prolog_flag(stack_limit, LimitBytes),
      NewLimit is LimitBytes * 2
    },
    [ nl,
      'Use the --stack_limit=size[KMG] command line option or'-[], nl,
      '?- set_prolog_flag(stack_limit, ~I). to double the limit.'-[NewLimit]
    ].


                 /*******************************
                 *        MAKE/AUTOLOAD         *
                 *******************************/

prolog_message(make(reload(Files))) -->
    { length(Files, N)
    },
    [ 'Make: reloading ~D files'-[N] ].
prolog_message(make(done(_Files))) -->
    [ 'Make: finished' ].
prolog_message(make(library_index(Dir))) -->
    [ 'Updating index for library ~w'-[Dir] ].
prolog_message(autoload(Pred, File)) -->
    thread_context,
    [ 'autoloading ~p from ~w'-[Pred, File] ].
prolog_message(autoload(read_index(Dir))) -->
    [ 'Loading autoload index for ~w'-[Dir] ].
prolog_message(autoload(disabled(Loaded))) -->
    [ 'Disabled autoloading (loaded ~D files)'-[Loaded] ].
prolog_message(autoload(already_defined(PI, From))) -->
    [ ansi(code, '~p', [PI]) ],
    (   { '$pi_head'(PI, Head),
          predicate_property(Head, built_in)
        }
    ->  [' is a built-in predicate']
    ;   [ ' is already imported from module ',
          ansi(code, '~p', [From])
        ]
    ).

swi_message(autoload(Msg)) -->
    [ nl, '  ' ],
    autoload_message(Msg).

autoload_message(not_exported(PI, Spec, _FullFile, _Exports)) -->
    [ ansi(code, '~w', [Spec]),
      ' does not export ',
      ansi(code, '~p', [PI])
    ].
autoload_message(no_file(Spec)) -->
    [ ansi(code, '~p', [Spec]), ': No such file' ].


                 /*******************************
                 *       COMPILER WARNINGS      *
                 *******************************/

% print warnings about dubious code raised by the compiler.
% TBD: pass in PC to produce exact error locations.

prolog_message(compiler_warnings(Clause, Warnings0)) -->
    {   print_goal_options(DefOptions),
        (   prolog_load_context(variable_names, VarNames)
        ->  warnings_with_named_vars(Warnings0, VarNames, Warnings),
            Options = [variable_names(VarNames)|DefOptions]
        ;   Options = DefOptions,
            Warnings = Warnings0
        )
    },
    compiler_warnings(Warnings, Clause, Options).

warnings_with_named_vars([], _, []).
warnings_with_named_vars([H|T0], VarNames, [H|T]) :-
    term_variables(H, Vars),
    '$member'(V1, Vars),
    '$member'(_=V2, VarNames),
    V1 == V2,
    !,
    warnings_with_named_vars(T0, VarNames, T).
warnings_with_named_vars([_|T0], VarNames, T) :-
    warnings_with_named_vars(T0, VarNames, T).


compiler_warnings([], _, _) --> [].
compiler_warnings([H|T], Clause, Options) -->
    (   compiler_warning(H, Clause, Options)
    ->  []
    ;   [ 'Unknown compiler warning: ~W'-[H,Options] ]
    ),
    (   {T==[]}
    ->  []
    ;   [nl]
    ),
    compiler_warnings(T, Clause, Options).

compiler_warning(eq_vv(A,B), _Clause, Options) -->
    (   { A == B }
    ->  [ 'Test is always true: ~W'-[A==B, Options] ]
    ;   [ 'Test is always false: ~W'-[A==B, Options] ]
    ).
compiler_warning(eq_singleton(A,B), _Clause, Options) -->
    [ 'Test is always false: ~W'-[A==B, Options] ].
compiler_warning(neq_vv(A,B), _Clause, Options) -->
    (   { A \== B }
    ->  [ 'Test is always true: ~W'-[A\==B, Options] ]
    ;   [ 'Test is always false: ~W'-[A\==B, Options] ]
    ).
compiler_warning(neq_singleton(A,B), _Clause, Options) -->
    [ 'Test is always true: ~W'-[A\==B, Options] ].
compiler_warning(unify_singleton(A,B), _Clause, Options) -->
    [ 'Unified variable is not used: ~W'-[A=B, Options] ].
compiler_warning(always(Bool, Pred, Arg), _Clause, Options) -->
    { Goal =.. [Pred,Arg] },
    [ 'Test is always ~w: ~W'-[Bool, Goal, Options] ].
compiler_warning(unbalanced_var(V), _Clause, Options) -->
    [ 'Variable not introduced in all branches: ~W'-[V, Options] ].
compiler_warning(branch_singleton(V), _Clause, Options) -->
    [ 'Singleton variable in branch: ~W'-[V, Options] ].
compiler_warning(negation_singleton(V), _Clause, Options) -->
    [ 'Singleton variable in \\+: ~W'-[V, Options] ].
compiler_warning(multiton(V), _Clause, Options) -->
    [ 'Singleton-marked variable appears more than once: ~W'-[V, Options] ].

print_goal_options(
    [ quoted(true),
      portray(true)
    ]).


                 /*******************************
                 *      TOPLEVEL MESSAGES       *
                 *******************************/

prolog_message(version) -->
    { current_prolog_flag(version_git, Version) },
    !,
    [ '~w'-[Version] ].
prolog_message(version) -->
    { current_prolog_flag(version_data, swi(Major,Minor,Patch,Options))
    },
    (   { memberchk(tag(Tag), Options) }
    ->  [ '~w.~w.~w-~w'-[Major, Minor, Patch, Tag] ]
    ;   [ '~w.~w.~w'-[Major, Minor, Patch] ]
    ).
prolog_message(address_bits) -->
    { current_prolog_flag(address_bits, Bits)
    },
    !,
    [ '~d bits, '-[Bits] ].
prolog_message(threads) -->
    { current_prolog_flag(threads, true)
    },
    !,
    [ 'threaded, ' ].
prolog_message(threads) -->
    [].
prolog_message(copyright) -->
    ['\33\[48;2;0;0;0m\33\[38;2;0;0;0m                           \33\[38;2;6;3;3m \33\[38;2;13;10;7m▁\33\[38;2;0;0;0m                                     \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m              \33\[38;2;8;8;8m \33\[38;2;18;18;18m \33\[38;2;1;1;1m▃\33\[38;2;101;90;77m▂\33\[38;2;100;90;78m▁\33\[48;2;1;1;1m\33\[38;2;80;67;57m▄\33\[48;2;15;13;12m\33\[38;2;90;80;69m▗\33\[48;2;7;5;4m\33\[38;2;88;73;62m▄\33\[48;2;4;3;2m\33\[38;2;69;52;47m▅\33\[48;2;31;23;22m\33\[38;2;78;65;57m━\33\[48;2;1;1;0m\33\[38;2;54;39;38m▆\33\[48;2;25;19;19m\33\[38;2;63;49;48m▅\33\[48;2;23;15;15m\33\[38;2;59;46;45m▆\33\[48;2;32;19;16m\33\[38;2;50;38;36m▅\33\[48;2;37;24;20m\33\[38;2;46;33;29m▃\33\[48;2;12;10;8m\33\[38;2;39;26;23m▆\33\[48;2;8;7;5m\33\[38;2;46;35;31m▅\33\[48;2;0;0;0m\33\[38;2;7;6;5m▃\33\[38;2;11;9;7m \33\[38;2;14;13;11m \33\[38;2;79;63;54m▁\33\[38;2;66;54;46m▂\33\[38;2;77;63;55m▂\33\[38;2;69;58;50m \33\[38;2;0;0;0m                            \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m          \33\[38;2;3;3;3m \33\[38;2;6;6;6m━\33\[38;2;9;9;9m─\33\[38;2;13;13;13m⎻\33\[48;2;21;19;18m\33\[38;2;75;64;62m▂\33\[48;2;41;37;33m\33\[38;2;111;94;82m▅\33\[48;2;67;62;56m\33\[38;2;101;88;79m▇\33\[48;2;104;88;75m\33\[38;2;94;76;67m▄\33\[48;2;101;88;76m\33\[38;2;66;49;45m▂\33\[48;2;84;67;59m\33\[38;2;71;55;50m┏\33\[48;2;103;84;73m\33\[38;2;95;78;69m▄\33\[48;2;70;54;49m\33\[38;2;99;84;75m▌\33\[48;2;46;31;30m\33\[38;2;70;52;48m▘\33\[48;2;51;37;37m\33\[38;2;39;25;24m▄\33\[48;2;47;31;30m\33\[38;2;64;50;50m╴\33\[48;2;46;29;27m\33\[38;2;50;35;33m▂\33\[48;2;49;36;34m\33\[38;2;76;65;63m▃\33\[48;2;52;40;37m\33\[38;2;73;63;62m▃\33\[48;2;39;25;22m\33\[38;2;39;25;24m▄\33\[48;2;47;34;32m\33\[38;2;30;16;16m▄\33\[48;2;36;23;21m\33\[38;2;51;39;36m⎻\33\[48;2;49;39;37m\33\[38;2;44;30;27m▄\33\[48;2;14;11;9m\33\[38;2;52;38;37m▇\33\[48;2;10;8;7m\33\[38;2;50;36;34m▆\33\[48;2;52;39;38m\33\[38;2;52;40;40m▄\33\[48;2;73;62;59m\33\[38;2;56;43;42m▊\33\[48;2;88;75;67m\33\[38;2;61;46;44m▄\33\[48;2;52;36;30m\33\[38;2;75;58;50m▘\33\[48;2;40;33;27m\33\[38;2;52;36;32m▄\33\[48;2;5;3;2m\33\[38;2;65;49;43m▆\33\[48;2;19;14;12m\33\[38;2;70;55;51m▄\33\[48;2;9;7;6m\33\[38;2;70;55;48m▅\33\[48;2;17;14;13m\33\[38;2;52;37;35m▅\33\[48;2;29;28;28m\33\[38;2;48;40;36m▄\33\[48;2;16;14;12m\33\[38;2;59;47;41m▅\33\[48;2;11;9;7m\33\[38;2;57;48;40m▂\33\[48;2;0;0;0m\33\[38;2;21;19;16m \33\[38;2;0;0;0m                   \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m             \33\[38;2;85;80;76m \33\[48;2;66;55;53m\33\[38;2;17;14;14m╸\33\[48;2;103;86;75m\33\[38;2;64;49;47m▆\33\[48;2;80;63;59m\33\[38;2;34;23;22m▅\33\[48;2;77;65;62m\33\[38;2;38;27;27m▆\33\[48;2;41;29;29m\33\[38;2;61;48;48m▁\33\[48;2;63;49;48m\33\[38;2;50;35;34m▚\33\[48;2;81;68;59m\33\[38;2;41;27;23m▇\33\[48;2;36;22;20m\33\[38;2;50;37;32m▘\33\[48;2;43;30;27m\33\[38;2;31;17;16m▇\33\[48;2;48;34;33m\33\[38;2;34;20;20m▅\33\[48;2;34;20;18m\33\[38;2;40;26;24m╸\33\[48;2;46;32;30m\33\[38;2;34;20;19m▇\33\[48;2;53;41;39m\33\[38;2;27;14;13m▆\33\[48;2;47;34;33m\33\[38;2;22;10;9m▇\33\[48;2;29;17;15m\33\[38;2;41;27;26m╶\33\[48;2;30;19;17m\33\[38;2;38;27;24m╴\33\[48;2;30;18;16m\33\[38;2;24;12;11m▃\33\[48;2;33;20;19m\33\[38;2;48;35;34m╺\33\[48;2;48;34;34m\33\[38;2;47;34;33m▄\33\[48;2;87;76;75m\33\[38;2;50;38;38m▅\33\[48;2;74;62;61m\33\[38;2;54;40;39m▆\33\[48;2;70;58;57m\33\[38;2;45;30;29m▅\33\[48;2;45;31;30m\33\[38;2;45;32;30m▄\33\[48;2;33;19;18m\33\[38;2;34;21;19m▄\33\[48;2;45;29;26m\33\[38;2;52;37;36m▁\33\[48;2;42;27;24m\33\[38;2;54;38;36m▝\33\[48;2;55;38;36m\33\[38;2;30;17;16m▄\33\[48;2;54;40;38m\33\[38;2;33;21;19m▄\33\[48;2;51;37;34m\33\[38;2;41;28;23m▄\33\[48;2;52;37;35m\33\[38;2;72;58;54m╺\33\[48;2;53;39;38m\33\[38;2;66;54;47m╴\33\[48;2;50;36;33m\33\[38;2;61;49;45m━\33\[48;2;43;31;26m\33\[38;2;0;0;0m \33\[48;2;16;12;10m\33\[38;2;48;35;29m▖\33\[48;2;0;0;0m\33\[38;2;0;0;0m                  \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m         \33\[38;2;3;2;2m \33\[48;2;88;65;55m\33\[38;2;0;0;0m▊\33\[48;2;31;27;24m\33\[38;2;85;66;58m▂\33\[48;2;21;20;18m\33\[38;2;75;63;57m▇\33\[48;2;62;46;46m\33\[38;2;0;0;0m \33\[48;2;53;36;36m\33\[38;2;58;40;40m▄\33\[48;2;49;32;33m\33\[38;2;67;51;51m▗\33\[48;2;54;40;40m\33\[38;2;60;45;45m▄\33\[48;2;57;43;44m\33\[38;2;57;40;41m▄\33\[48;2;61;48;47m\33\[38;2;53;38;39m▆\33\[48;2;48;32;30m\33\[38;2;56;42;41m━\33\[48;2;35;21;20m\33\[38;2;48;34;31m▇\33\[48;2;37;23;20m\33\[38;2;40;26;23m▄\33\[48;2;30;16;15m\33\[38;2;30;16;14m▄\33\[48;2;34;20;19m\33\[38;2;38;25;24m▄\33\[48;2;33;19;19m\33\[38;2;50;37;37m╸\33\[48;2;32;19;18m\33\[38;2;33;20;19m▄\33\[48;2;33;21;20m\33\[38;2;0;0;0m \33\[48;2;25;14;12m\33\[38;2;27;17;15m▄\33\[48;2;25;15;13m\33\[38;2;19;8;7m▊\33\[48;2;32;22;21m\33\[38;2;0;0;0m \33\[48;2;30;19;17m\33\[38;2;37;26;24m▂\33\[48;2;37;23;22m\33\[38;2;36;24;23m▄\33\[48;2;51;38;38m\33\[38;2;32;18;17m▆\33\[48;2;67;57;56m\33\[38;2;37;22;21m▆\33\[48;2;47;34;33m\33\[38;2;0;0;0m \33\[48;2;72;61;61m\33\[38;2;34;20;20m▃\33\[48;2;46;32;31m\33\[38;2;59;46;45m▎\33\[48;2;43;28;24m\33\[38;2;50;36;35m▆\33\[48;2;43;27;25m\33\[38;2;57;41;40m┻\33\[48;2;40;25;22m\33\[38;2;0;0;0m \33\[48;2;26;12;12m\33\[38;2;35;21;19m▆\33\[48;2;27;14;13m\33\[38;2;21;8;8m▘\33\[48;2;26;14;12m\33\[38;2;31;17;16m▖\33\[48;2;31;19;14m\33\[38;2;42;27;23m▝\33\[48;2;36;22;18m\33\[38;2;29;16;12m▄\33\[48;2;41;27;24m\33\[38;2;0;0;0m \33\[48;2;42;28;24m \33\[48;2;46;33;26m\33\[38;2;40;25;21m▆\33\[48;2;40;32;26m\33\[38;2;63;50;42m▄\33\[48;2;10;9;8m\33\[38;2;62;53;45m▄\33\[48;2;0;0;0m\33\[38;2;73;57;48m▁\33\[38;2;28;21;16m \33\[38;2;0;0;0m              \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;2;2;2m \33\[38;2;0;0;0m       \33\[38;2;50;45;45m \33\[48;2;40;36;32m\33\[38;2;83;65;59m▆\33\[48;2;90;77;73m\33\[38;2;87;63;56m▃\33\[48;2;83;60;54m\33\[38;2;69;50;46m▁\33\[48;2;80;61;57m\33\[38;2;68;49;49m▇\33\[48;2;63;48;49m\33\[38;2;96;83;83m╺\33\[48;2;60;45;44m\33\[38;2;82;69;70m╸\33\[48;2;56;38;38m\33\[38;2;50;32;29m▅\33\[48;2;60;46;47m\33\[38;2;38;22;21m▄\33\[48;2;50;34;32m\33\[38;2;45;31;28m▄\33\[48;2;52;35;33m\33\[38;2;48;30;27m▄\33\[48;2;47;29;27m\33\[38;2;45;29;26m▄\33\[48;2;38;23;22m\33\[38;2;48;34;32m▁\33\[48;2;34;20;18m\33\[38;2;0;0;0m \33\[38;2;38;22;20m▆\33\[48;2;34;19;19m\33\[38;2;45;28;26m▃\33\[48;2;40;28;27m\33\[38;2;62;51;51m┏\33\[48;2;37;23;22m\33\[38;2;49;38;36m▌\33\[48;2;28;15;14m\33\[38;2;25;14;12m▄\33\[48;2;23;13;11m\33\[38;2;29;18;16m▗\33\[48;2;25;15;13m\33\[38;2;38;28;25m╶\33\[48;2;27;16;15m\33\[38;2;0;0;0m \33\[48;2;26;15;13m\33\[38;2;37;28;25m╺\33\[48;2;45;32;32m\33\[38;2;81;75;80m╺\33\[48;2;50;37;37m\33\[38;2;73;62;65m╴\33\[48;2;52;37;36m\33\[38;2;0;0;0m \33\[48;2;28;14;14m\33\[38;2;37;21;20m▄\33\[48;2;29;15;15m\33\[38;2;38;22;21m▂\33\[48;2;26;12;11m\33\[38;2;29;17;16m▄\33\[48;2;30;16;15m\33\[38;2;17;8;5m▆\33\[48;2;27;14;12m\33\[38;2;31;19;18m▄\33\[48;2;30;15;15m\33\[38;2;0;0;0m \33\[48;2;35;21;20m\33\[38;2;22;8;8m▆\33\[48;2;21;9;8m\33\[38;2;0;0;0m \33\[48;2;30;18;17m \33\[48;2;46;32;28m\33\[38;2;109;95;96m▂\33\[48;2;47;32;30m\33\[38;2;0;0;0m \33\[48;2;39;25;24m \33\[48;2;30;16;14m\33\[38;2;65;54;51m▘\33\[48;2;35;22;18m\33\[38;2;27;14;12m▇\33\[48;2;43;30;25m\33\[38;2;31;17;16m▅\33\[48;2;43;32;26m\33\[38;2;39;26;22m▄\33\[48;2;52;37;30m\33\[38;2;28;16;11m▄\33\[48;2;44;37;31m\33\[38;2;24;11;9m▃\33\[48;2;10;9;7m\33\[38;2;37;27;23m▃\33\[48;2;0;0;0m\33\[38;2;52;46;39m \33\[38;2;0;0;0m            \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m       \33\[38;2;20;16;14m \33\[48;2;75;60;56m\33\[38;2;4;3;3m▘\33\[48;2;70;49;48m\33\[38;2;110;90;88m▘\33\[48;2;71;52;51m\33\[38;2;67;47;48m⎻\33\[48;2;70;52;51m\33\[38;2;55;37;37m▂\33\[48;2;65;47;47m\33\[38;2;51;32;29m▂\33\[48;2;68;52;52m\33\[38;2;62;46;45m▄\33\[48;2;65;50;50m\33\[38;2;80;66;67m━\33\[48;2;49;31;27m\33\[38;2;57;43;43m▖\33\[48;2;43;28;25m\33\[38;2;55;40;39m▖\33\[48;2;45;31;28m\33\[38;2;53;40;39m╷\33\[48;2;42;24;24m\33\[38;2;50;34;33m▁\33\[48;2;42;27;24m\33\[38;2;38;22;22m▄\33\[48;2;41;26;24m\33\[38;2;59;47;45m╵\33\[48;2;49;32;31m\33\[38;2;58;42;44m▄\33\[48;2;50;32;31m\33\[38;2;51;34;33m▄\33\[48;2;59;47;47m\33\[38;2;48;31;30m▌\33\[48;2;42;29;29m\33\[38;2;58;47;47m▖\33\[48;2;28;17;16m\33\[38;2;46;33;32m▁\33\[48;2;36;23;22m\33\[38;2;42;29;28m┏\33\[48;2;36;24;22m\33\[38;2;63;52;54m▗\33\[48;2;34;21;20m\33\[38;2;69;60;62m▄\33\[48;2;30;18;16m\33\[38;2;0;0;0m \33\[48;2;26;13;12m \33\[48;2;28;15;14m \33\[48;2;42;29;28m \33\[48;2;44;29;28m\33\[38;2;98;86;86m▘\33\[48;2;52;37;38m\33\[38;2;97;85;86m▗\33\[48;2;49;30;31m\33\[38;2;65;47;51m▌\33\[48;2;41;25;24m\33\[38;2;52;36;37m━\33\[48;2;38;27;25m\33\[38;2;60;51;50m━\33\[48;2;29;16;15m\33\[38;2;29;17;14m▄\33\[48;2;28;15;14m\33\[38;2;41;27;26m▂\33\[48;2;30;17;16m\33\[38;2;39;28;26m▗\33\[48;2;27;16;14m\33\[38;2;45;35;31m▆\33\[48;2;46;33;31m\33\[38;2;0;0;0m \33\[48;2;106;93;93m\33\[38;2;40;25;23m▇\33\[48;2;38;21;18m\33\[38;2;23;8;7m▇\33\[48;2;25;11;10m\33\[38;2;34;20;19m⎼\33\[48;2;26;12;11m\33\[38;2;35;21;20m⎼\33\[48;2;28;14;13m\33\[38;2;38;24;21m▖\33\[48;2;38;25;24m\33\[38;2;0;0;0m \33\[48;2;44;35;31m\33\[38;2;30;17;16m▆\33\[48;2;28;18;14m\33\[38;2;20;8;7m▅\33\[48;2;23;12;11m\33\[38;2;33;21;19m⎺\33\[48;2;39;25;23m\33\[38;2;34;20;19m▊\33\[48;2;45;34;30m\33\[38;2;57;43;36m┣\33\[48;2;0;0;0m\33\[38;2;69;60;52m \33\[38;2;0;0;0m           \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m       \33\[48;2;19;16;16m\33\[38;2;63;54;51m▗\33\[48;2;84;62;58m\33\[38;2;0;0;0m \33\[48;2;75;52;52m\33\[38;2;79;58;59m▝\33\[48;2;61;43;44m\33\[38;2;63;44;45m▄\33\[48;2;54;39;39m\33\[38;2;52;37;37m▄\33\[48;2;52;35;33m\33\[38;2;72;59;58m▁\33\[48;2;43;24;24m\33\[38;2;55;40;41m▂\33\[48;2;31;16;15m\33\[38;2;0;0;0m \33\[48;2;43;27;26m\33\[38;2;29;15;14m▅\33\[48;2;47;34;32m\33\[38;2;34;20;18m▆\33\[48;2;42;28;26m\33\[38;2;0;0;0m \33\[48;2;53;38;38m\33\[38;2;72;59;60m▁\33\[48;2;58;44;43m\33\[38;2;84;73;75m▅\33\[48;2;84;71;71m\33\[38;2;57;41;40m▅\33\[48;2;44;26;25m\33\[38;2;42;24;24m▄\33\[48;2;41;22;22m\33\[38;2;58;43;45m▃\33\[48;2;56;41;42m\33\[38;2;51;36;36m▄\33\[48;2;36;22;22m\33\[38;2;22;9;9m▃\33\[48;2;38;25;24m\33\[38;2;18;8;7m▅\33\[38;2;64;53;52m╺\33\[48;2;32;18;17m\33\[38;2;47;34;32m▖\33\[48;2;41;29;28m\33\[38;2;43;30;30m▄\33\[48;2;38;25;23m\33\[38;2;57;44;43m▖\33\[48;2;31;17;16m\33\[38;2;42;29;27m▘\33\[48;2;20;7;7m\33\[38;2;36;20;20m▁\33\[48;2;32;18;17m\33\[38;2;24;10;9m▎\33\[48;2;45;30;28m\33\[38;2;52;38;38m▁\33\[48;2;75;63;64m\33\[38;2;47;31;30m▆\33\[48;2;78;63;65m\33\[38;2;56;41;43m▁\33\[48;2;41;26;25m\33\[38;2;66;52;52m╸\33\[48;2;19;8;8m\33\[38;2;28;13;13m▁\33\[48;2;19;8;7m\33\[38;2;0;0;0m \33\[48;2;26;13;13m\33\[38;2;43;29;27m▝\33\[48;2;37;28;25m\33\[38;2;27;14;13m▇\33\[48;2;25;13;12m\33\[38;2;0;0;0m \33\[48;2;60;49;47m\33\[38;2;34;21;20m▇\33\[48;2;47;34;32m\33\[38;2;74;64;65m━\33\[48;2;29;16;16m\33\[38;2;32;18;15m▄\33\[48;2;31;17;17m\33\[38;2;47;34;32m▁\33\[48;2;42;29;29m\33\[38;2;64;51;53m╴\33\[48;2;29;15;14m\33\[38;2;43;26;23m▖\33\[48;2;31;18;17m\33\[38;2;0;0;0m \33\[48;2;30;18;16m\33\[38;2;42;30;28m▖\33\[48;2;19;8;7m\33\[38;2;23;12;10m▖\33\[48;2;26;15;14m\33\[38;2;21;9;9m▊\33\[48;2;32;21;19m\33\[38;2;32;18;17m▄\33\[48;2;29;18;15m\33\[38;2;0;0;0m \33\[48;2;12;9;8m\33\[38;2;35;30;27m┓\33\[48;2;0;0;0m\33\[38;2;52;42;40m \33\[38;2;0;0;0m          \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m     \33\[38;2;29;24;24m \33\[38;2;96;72;71m▂\33\[48;2;20;16;16m\33\[38;2;73;53;52m▄\33\[48;2;72;48;48m\33\[38;2;55;34;35m▂\33\[48;2;60;40;40m\33\[38;2;73;52;53m▝\33\[48;2;69;51;52m\33\[38;2;0;0;0m \33\[48;2;61;47;48m\33\[38;2;71;55;55m⎺\33\[48;2;73;60;60m\33\[38;2;54;40;41m▄\33\[48;2;51;36;35m\33\[38;2;81;69;70m▘\33\[48;2;27;13;12m\33\[38;2;34;16;16m▎\33\[48;2;31;17;16m\33\[38;2;0;0;0m \33\[48;2;39;23;22m\33\[38;2;38;23;22m▄\33\[48;2;34;20;19m\33\[38;2;48;34;32m▆\33\[48;2;58;44;42m\33\[38;2;78;67;67m▝\33\[48;2;57;42;43m\33\[38;2;78;66;69m▘\33\[48;2;48;31;30m\33\[38;2;39;22;22m┓\33\[48;2;54;39;39m\33\[38;2;38;20;20m▂\33\[48;2;57;44;45m\33\[38;2;50;33;32m▅\33\[48;2;39;22;22m\33\[38;2;58;41;44m▂\33\[48;2;37;23;23m\33\[38;2;72;57;62m▄\33\[48;2;34;22;21m\33\[38;2;88;74;78m▂\33\[48;2;32;18;18m\33\[38;2;61;49;49m▁\33\[48;2;45;28;26m\33\[38;2;32;15;15m▗\33\[48;2;56;44;43m\33\[38;2;28;14;13m▇\33\[48;2;26;12;11m\33\[38;2;0;0;0m \33\[48;2;39;26;25m \33\[48;2;50;34;34m\33\[38;2;76;63;63m━\33\[48;2;37;21;21m\33\[38;2;51;40;39m╷\33\[48;2;46;30;29m\33\[38;2;57;44;43m▘\33\[48;2;44;25;25m\33\[38;2;59;45;47m▂\33\[48;2;37;21;21m\33\[38;2;51;36;37m▂\33\[48;2;31;16;15m\33\[38;2;48;33;32m╺\33\[48;2;41;29;28m\33\[38;2;62;52;52m▘\33\[48;2;34;22;21m\33\[38;2;58;47;47m╺\33\[48;2;33;20;19m\33\[38;2;81;71;73m▂\33\[48;2;29;15;14m\33\[38;2;38;24;23m┗\33\[48;2;28;14;13m\33\[38;2;39;26;25m▝\33\[38;2;41;27;26m━\33\[48;2;42;29;29m\33\[38;2;62;49;51m┗\33\[48;2;49;34;32m\33\[38;2;75;64;64m▄\33\[48;2;45;30;28m\33\[38;2;53;42;44m▝\33\[48;2;58;44;48m\33\[38;2;42;28;28m▂\33\[48;2;44;29;27m\33\[38;2;69;58;58m▖\33\[48;2;26;12;12m\33\[38;2;37;20;19m▄\33\[48;2;28;14;13m\33\[38;2;23;9;10m▚\33\[48;2;32;17;17m\33\[38;2;25;12;12m▄\33\[48;2;33;19;18m\33\[38;2;33;19;19m▄\33\[48;2;25;12;11m\33\[38;2;32;17;17m▄\33\[48;2;30;17;16m\33\[38;2;48;36;32m━\33\[48;2;36;23;18m\33\[38;2;28;16;12m▊\33\[48;2;56;47;42m\33\[38;2;60;49;43m▄\33\[48;2;0;0;0m\33\[38;2;53;47;41m▎\33\[38;2;0;0;0m         \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m    \33\[38;2;51;46;45m \33\[48;2;93;73;70m\33\[38;2;68;58;55m▎\33\[48;2;73;54;55m\33\[38;2;86;69;71m┏\33\[48;2;59;39;40m\33\[38;2;67;48;50m▄\33\[48;2;55;35;37m\33\[38;2;72;56;57m▄\33\[48;2;63;44;44m\33\[38;2;0;0;0m \33\[48;2;69;53;53m\33\[38;2;51;31;28m▆\33\[48;2;64;51;51m\33\[38;2;46;28;28m▆\33\[48;2;52;35;34m\33\[38;2;45;26;26m▖\33\[48;2;51;36;36m\33\[38;2;58;43;44m▄\33\[48;2;33;16;16m\33\[38;2;50;32;30m▃\33\[48;2;40;23;22m\33\[38;2;48;29;26m▄\33\[48;2;50;32;31m\33\[38;2;0;0;0m \33\[48;2;49;32;31m\33\[38;2;61;49;48m▂\33\[48;2;53;40;40m\33\[38;2;47;32;29m▄\33\[48;2;42;27;25m\33\[38;2;41;25;25m▄\33\[48;2;51;35;34m\33\[38;2;68;55;55m▂\33\[48;2;46;27;27m\33\[38;2;0;0;0m \33\[48;2;42;23;24m \33\[48;2;73;59;64m\33\[38;2;48;30;31m▊\33\[48;2;79;65;71m\33\[38;2;93;76;83m▝\33\[48;2;71;56;59m\33\[38;2;43;25;21m▃\33\[48;2;68;55;55m\33\[38;2;32;12;10m▅\33\[48;2;33;15;14m\33\[38;2;0;0;0m \33\[48;2;35;18;17m\33\[38;2;35;17;13m▄\33\[38;2;44;27;25m▗\33\[48;2;26;11;10m\33\[38;2;34;17;16m▎\33\[48;2;27;11;10m\33\[38;2;0;0;0m \33\[48;2;38;22;21m \33\[48;2;41;24;25m\33\[38;2;52;33;33m▄\33\[48;2;53;36;37m\33\[38;2;95;86;91m▝\33\[48;2;90;77;80m\33\[38;2;62;46;47m▅\33\[48;2;37;21;21m\33\[38;2;0;0;0m \33\[48;2;24;10;10m\33\[38;2;21;7;8m┗\33\[48;2;29;15;15m\33\[38;2;0;0;0m \33\[48;2;76;66;68m\33\[38;2;43;29;29m▄\33\[48;2;53;40;40m\33\[38;2;69;57;60m━\33\[48;2;31;16;15m\33\[38;2;44;28;28m╸\33\[48;2;30;16;15m\33\[38;2;0;0;0m \33\[48;2;29;15;14m\33\[38;2;33;19;18m▄\33\[48;2;60;47;46m\33\[38;2;47;31;28m▆\33\[48;2;39;24;23m\33\[38;2;0;0;0m \33\[48;2;30;17;16m\33\[38;2;36;22;22m┫\33\[48;2;59;46;46m\33\[38;2;33;20;19m▌\33\[48;2;46;32;30m\33\[38;2;65;51;51m▌\33\[48;2;25;11;10m\33\[38;2;31;16;15m▘\33\[48;2;21;9;8m\33\[38;2;22;10;9m▄\33\[48;2;28;15;14m\33\[38;2;21;10;9m▄\33\[48;2;30;16;15m\33\[38;2;32;18;17m▄\33\[48;2;25;11;11m\33\[38;2;24;10;10m▄\33\[48;2;23;10;9m\33\[38;2;29;14;13m⎺\33\[48;2;46;35;30m\33\[38;2;30;17;15m▇\33\[48;2;13;11;10m\33\[38;2;47;39;31m▅\33\[48;2;0;0;0m\33\[38;2;41;37;31m \33\[38;2;0;0;0m        \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m  \33\[38;2;5;4;4m \33\[48;2;19;18;17m\33\[38;2;78;66;64m▗\33\[48;2;31;26;25m\33\[38;2;98;83;79m▅\33\[48;2;87;65;64m\33\[38;2;108;89;88m▖\33\[48;2;83;63;65m\33\[38;2;78;62;65m▄\33\[48;2;66;49;50m\33\[38;2;0;0;0m \33\[48;2;61;45;46m\33\[38;2;71;55;57m▎\33\[48;2;59;41;40m\33\[38;2;45;26;23m▆\33\[48;2;48;29;26m\33\[38;2;65;49;50m▝\33\[48;2;50;33;33m\33\[38;2;66;53;54m▘\33\[48;2;53;34;32m\33\[38;2;53;34;34m╸\33\[48;2;53;35;34m\33\[38;2;54;38;40m▗\33\[48;2;53;36;37m\33\[38;2;0;0;0m \33\[48;2;58;44;44m\33\[38;2;46;25;25m▅\33\[48;2;48;30;30m\33\[38;2;74;62;62m▝\33\[48;2;46;28;27m\33\[38;2;67;55;55m▘\33\[48;2;36;19;19m\33\[38;2;46;27;25m▌\33\[48;2;55;40;40m\33\[38;2;0;0;0m \33\[48;2;73;61;61m\33\[38;2;44;27;25m▄\33\[48;2;62;48;49m\33\[38;2;38;18;19m▄\33\[48;2;56;40;41m\33\[38;2;47;27;28m▄\33\[48;2;62;49;51m\33\[38;2;65;51;53m▄\33\[48;2;56;37;40m\33\[38;2;0;0;0m \33\[48;2;44;25;20m\33\[38;2;39;17;14m▆\33\[48;2;47;27;25m\33\[38;2;36;16;12m▊\33\[48;2;47;27;27m\33\[38;2;54;31;32m▄\33\[48;2;36;16;16m\33\[38;2;0;0;0m \33\[48;2;34;17;17m\33\[38;2;58;35;32m▂\33\[48;2;32;15;14m\33\[38;2;63;30;29m▂\33\[48;2;41;22;20m\33\[38;2;55;26;25m▂\33\[48;2;51;31;31m\33\[38;2;74;58;58m─\33\[48;2;48;29;28m\33\[38;2;73;59;60m▘\33\[48;2;54;35;37m\33\[38;2;89;76;81m▗\33\[48;2;74;58;59m\33\[38;2;116;105;110m▖\33\[48;2;54;35;35m\33\[38;2;70;53;54m━\33\[48;2;57;39;40m\33\[38;2;108;94;97m━\33\[48;2;42;24;23m\33\[38;2;59;46;46m┛\33\[48;2;36;17;15m\33\[38;2;44;25;23m⎽\33\[48;2;46;29;28m\33\[38;2;52;41;41m▝\33\[48;2;32;18;18m\33\[38;2;65;53;53m▆\33\[48;2;33;20;18m\33\[38;2;64;51;53m▅\33\[48;2;47;32;31m\33\[38;2;60;47;49m▃\33\[48;2;46;29;28m\33\[38;2;51;33;32m▄\33\[48;2;43;26;23m\33\[38;2;42;26;23m▄\33\[48;2;26;12;12m\33\[38;2;34;19;18m┛\33\[48;2;24;11;10m\33\[38;2;50;37;37m▝\33\[48;2;48;32;32m\33\[38;2;33;18;17m▆\33\[48;2;28;15;14m\33\[38;2;42;28;27m▌\33\[48;2;25;13;12m\33\[38;2;37;22;21m▁\33\[48;2;29;16;15m\33\[38;2;37;24;23m╷\33\[48;2;30;16;15m\33\[38;2;32;18;18m▃\33\[48;2;26;13;12m\33\[38;2;31;17;17m▗\33\[48;2;24;11;10m\33\[38;2;0;0;0m \33\[48;2;33;21;17m\33\[38;2;32;20;17m▄\33\[48;2;46;35;27m\33\[38;2;31;20;14m▅\33\[48;2;12;10;9m\33\[38;2;35;23;18m▆\33\[48;2;19;15;13m\33\[38;2;63;49;42m━\33\[48;2;0;0;0m\33\[38;2;35;33;31m \33\[38;2;0;0;0m      \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m  \33\[38;2;25;25;25m \33\[48;2;99;93;91m\33\[38;2;49;46;45m▄\33\[48;2;132;124;118m\33\[38;2;103;91;88m▄\33\[48;2;85;69;68m\33\[38;2;102;85;86m▖\33\[48;2;62;47;48m\33\[38;2;76;60;61m─\33\[48;2;90;75;81m\33\[38;2;62;47;49m▅\33\[48;2;47;26;26m\33\[38;2;52;33;34m▎\33\[48;2;50;31;28m\33\[38;2;0;0;0m \33\[38;2;60;43;42m▁\33\[48;2;50;32;30m\33\[38;2;52;34;33m▄\33\[48;2;52;34;34m\33\[38;2;0;0;0m \33\[48;2;53;33;32m\33\[38;2;56;40;42m─\33\[48;2;54;35;36m\33\[38;2;55;37;37m▄\33\[48;2;48;27;29m\33\[38;2;73;58;58m▄\33\[48;2;51;31;30m\33\[38;2;66;48;48m▖\33\[48;2;38;18;14m\33\[38;2;49;29;26m▁\33\[48;2;38;19;14m\33\[38;2;47;27;26m▝\33\[48;2;47;29;28m\33\[38;2;42;24;23m▄\33\[48;2;38;19;14m\33\[38;2;43;24;19m▄\33\[48;2;38;18;15m\33\[38;2;56;37;37m▂\33\[48;2;42;22;18m\33\[38;2;51;32;30m▁\33\[48;2;63;47;48m\33\[38;2;50;28;26m▇\33\[48;2;53;29;29m\33\[38;2;0;0;0m \33\[48;2;48;23;21m\33\[38;2;53;29;31m▚\33\[48;2;45;20;16m\33\[38;2;0;0;0m \33\[48;2;50;23;22m\33\[38;2;62;36;38m▗\33\[48;2;85;59;61m\33\[38;2;121;99;101m━\33\[48;2;74;45;43m\33\[38;2;102;77;79m▘\33\[48;2;81;44;42m\33\[38;2;60;29;28m▅\33\[48;2;50;19;17m\33\[38;2;61;28;27m▎\33\[48;2;40;15;15m\33\[38;2;0;0;0m \33\[48;2;42;20;18m\33\[38;2;54;32;33m▗\33\[48;2;46;25;26m\33\[38;2;72;52;56m▁\33\[48;2;55;35;37m\33\[38;2;86;69;72m▁\33\[48;2;52;31;30m\33\[38;2;73;52;54m▁\33\[48;2;47;25;25m\33\[38;2;91;72;73m╴\33\[48;2;41;19;18m\33\[38;2;47;26;23m─\33\[48;2;42;22;17m\33\[38;2;36;15;12m▃\33\[48;2;42;23;19m\33\[38;2;0;0;0m \33\[48;2;41;24;23m\33\[38;2;64;51;51m╸\33\[48;2;60;47;47m\33\[38;2;34;18;17m▇\33\[48;2;40;26;25m\33\[38;2;59;49;48m╺\33\[48;2;55;41;42m\33\[38;2;42;25;25m▄\33\[48;2;38;22;21m\33\[38;2;48;33;33m┛\33\[48;2;29;15;15m\33\[38;2;33;18;17m▄\33\[48;2;26;13;13m\33\[38;2;41;29;28m⎼\33\[48;2;26;12;12m\33\[38;2;44;30;29m▃\33\[48;2;37;23;21m\33\[38;2;50;39;37m━\33\[48;2;36;22;20m\33\[38;2;47;34;34m▅\33\[48;2;31;17;16m\33\[38;2;41;27;25m▌\33\[48;2;43;28;26m\33\[38;2;74;61;61m▃\33\[48;2;29;15;14m\33\[38;2;43;29;27m▃\33\[48;2;23;11;10m\33\[38;2;36;25;23m▗\33\[48;2;21;9;8m\33\[38;2;0;0;0m \33\[48;2;22;11;10m\33\[38;2;25;14;12m╵\33\[48;2;24;12;11m\33\[38;2;35;22;20m▝\33\[48;2;51;36;31m\33\[38;2;28;16;14m▄\33\[48;2;19;16;14m\33\[38;2;52;41;36m▃\33\[48;2;0;0;0m\33\[38;2;6;5;4m▂\33\[38;2;39;32;25m     \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m   \33\[38;2;4;4;4m▄\33\[48;2;63;60;59m\33\[38;2;85;71;69m▅\33\[48;2;80;64;64m\33\[38;2;0;0;0m \33\[48;2;72;56;57m\33\[38;2;56;41;42m▗\33\[48;2;55;40;42m\33\[38;2;49;34;36m┣\33\[48;2;55;39;40m\33\[38;2;68;51;51m▂\33\[48;2;63;44;45m\33\[38;2;79;61;62m━\33\[48;2;61;42;42m\33\[38;2;56;38;38m▄\33\[48;2;49;29;26m\33\[38;2;0;0;0m \33\[48;2;50;30;28m\33\[38;2;54;37;38m┗\33\[48;2;51;31;32m\33\[38;2;54;37;39m─\33\[48;2;58;44;45m\33\[38;2;49;28;27m▅\33\[48;2;57;38;39m\33\[38;2;88;71;71m⎼\33\[48;2;61;41;42m\33\[38;2;74;55;56m▘\33\[48;2;50;29;30m\33\[38;2;62;41;43m━\33\[48;2;45;23;21m\33\[38;2;64;44;44m╸\33\[48;2;42;23;19m\33\[38;2;58;32;31m▃\33\[48;2;56;32;31m\33\[38;2;92;51;49m▁\33\[48;2;60;37;38m\33\[38;2;108;57;58m▂\33\[48;2;69;44;46m\33\[38;2;134;76;74m▁\33\[48;2;64;38;39m\33\[38;2;134;76;72m▁\33\[48;2;59;30;30m\33\[38;2;139;72;68m▁\33\[48;2;60;29;30m\33\[38;2;132;66;60m▁\33\[48;2;71;34;34m\33\[38;2;124;59;54m▁\33\[48;2;58;25;24m\33\[38;2;135;70;60m▂\33\[48;2;70;38;37m\33\[38;2;150;89;76m▂\33\[48;2;88;48;46m\33\[38;2;183;119;105m▁\33\[48;2;69;32;30m\33\[38;2;173;112;103m▂\33\[48;2;55;21;20m\33\[38;2;159;98;90m▃\33\[48;2;54;22;22m\33\[38;2;160;100;90m▃\33\[48;2;62;31;32m\33\[38;2;146;86;79m▄\33\[48;2;81;50;52m\33\[38;2;135;75;68m▄\33\[48;2;98;74;78m\33\[38;2;96;54;51m▄\33\[48;2;68;44;45m\33\[38;2;110;80;80m▁\33\[48;2;54;28;28m\33\[38;2;0;0;0m \33\[48;2;40;17;16m\33\[38;2;59;33;36m▄\33\[48;2;43;21;17m\33\[38;2;61;32;34m▅\33\[48;2;41;20;16m\33\[38;2;56;30;31m▖\33\[48;2;44;25;20m\33\[38;2;38;19;14m▊\33\[48;2;37;19;17m\33\[38;2;45;26;22m▌\33\[48;2;44;29;28m\33\[38;2;37;19;17m▇\33\[48;2;26;10;10m\33\[38;2;36;19;18m▎\33\[48;2;24;10;9m\33\[38;2;30;15;13m▁\33\[48;2;24;10;10m\33\[38;2;36;21;21m▗\33\[48;2;33;20;19m\33\[38;2;45;31;31m╸\33\[48;2;45;31;31m\33\[38;2;37;24;23m▄\33\[48;2;39;26;24m\33\[38;2;47;34;34m━\33\[48;2;36;22;21m\33\[38;2;57;44;44m▁\33\[48;2;44;31;30m\33\[38;2;41;26;24m▄\33\[48;2;57;44;43m\33\[38;2;36;20;19m▆\33\[48;2;30;16;15m\33\[38;2;0;0;0m \33\[48;2;24;11;9m \33\[48;2;21;8;7m\33\[38;2;26;12;11m▌\33\[48;2;20;8;8m\33\[38;2;16;6;4m▗\33\[48;2;19;8;7m\33\[38;2;15;5;3m▂\33\[38;2;0;0;0m \33\[48;2;28;17;14m \33\[48;2;59;47;38m\33\[38;2;96;86;76m╹\33\[48;2;0;0;0m\33\[38;2;16;13;11m▌    \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m  \33\[38;2;2;2;2m╴\33\[48;2;95;85;84m\33\[38;2;7;7;7m▎\33\[48;2;67;52;51m\33\[38;2;109;95;94m▌\33\[48;2;74;57;57m\33\[38;2;64;49;49m▄\33\[48;2;54;39;39m\33\[38;2;64;48;49m▊\33\[48;2;59;44;44m\33\[38;2;0;0;0m \33\[48;2;75;57;58m\33\[38;2;96;79;79m╷\33\[48;2;66;46;48m\33\[38;2;75;56;57m┗\33\[48;2;53;33;33m\33\[38;2;59;39;41m▊\33\[48;2;48;28;24m\33\[38;2;55;34;36m▂\33\[48;2;49;29;26m\33\[38;2;66;47;49m▂\33\[48;2;48;27;23m\33\[38;2;50;29;28m▁\33\[48;2;47;25;21m\33\[38;2;54;31;31m▗\33\[48;2;54;31;33m\33\[38;2;62;39;41m━\33\[48;2;66;37;37m\33\[38;2;104;61;57m▗\33\[48;2;67;39;41m\33\[38;2;120;72;67m▅\33\[48;2;97;52;51m\33\[38;2;150;97;90m▄\33\[48;2;117;63;59m\33\[38;2;170;110;103m▅\33\[48;2;120;63;61m\33\[38;2;178;117;111m▆\33\[48;2;163;100;94m\33\[38;2;195;137;128m▆\33\[48;2;183;122;117m\33\[38;2;215;159;153m▆\33\[48;2;181;117;112m\33\[38;2;218;161;156m▆\33\[48;2;184;121;112m\33\[38;2;217;158;151m▆\33\[48;2;165;95;85m\33\[38;2;212;150;144m▇\33\[48;2;172;99;88m\33\[38;2;211;145;135m▆\33\[48;2;182;110;95m\33\[38;2;224;164;153m▆\33\[48;2;196;128;110m\33\[38;2;226;166;156m▆\33\[48;2;202;137;122m\33\[38;2;224;162;152m▆\33\[48;2;211;148;137m\33\[38;2;223;161;151m▄\33\[48;2;202;136;126m\33\[38;2;213;149;139m▄\33\[48;2;196;129;120m\33\[38;2;210;148;138m▅\33\[48;2;187;120;108m\33\[38;2;203;139;127m▅\33\[48;2;169;101;85m\33\[38;2;190;124;109m▅\33\[48;2;134;78;73m\33\[38;2;168;103;92m▊\33\[48;2;99;56;55m\33\[38;2;75;43;43m▝\33\[48;2;80;50;49m\33\[38;2;70;39;39m▄\33\[48;2;82;49;49m\33\[38;2;61;33;35m▁\33\[48;2;76;41;41m\33\[38;2;54;24;24m▂\33\[48;2;53;27;28m\33\[38;2;61;34;35m▄\33\[48;2;46;22;20m\33\[38;2;49;26;27m▂\33\[48;2;40;19;15m\33\[38;2;0;0;0m \33\[48;2;37;19;14m \33\[48;2;36;18;13m\33\[38;2;42;23;17m┓\33\[48;2;33;15;13m\33\[38;2;54;37;36m▂\33\[48;2;51;33;33m\33\[38;2;71;57;56m▂\33\[48;2;44;25;24m\33\[38;2;63;48;47m▖\33\[48;2;30;15;14m\33\[38;2;40;21;21m▖\33\[48;2;38;23;22m\33\[38;2;0;0;0m \33\[48;2;38;25;25m\33\[38;2;80;69;68m▘\33\[48;2;27;13;12m\33\[38;2;31;17;15m╴\33\[48;2;32;18;17m\33\[38;2;44;30;28m▗\33\[38;2;43;28;26m▂\33\[48;2;27;13;12m\33\[38;2;42;28;25m▃\33\[48;2;23;10;9m\33\[38;2;30;16;15m▅\33\[48;2;20;8;7m\33\[38;2;26;14;12m▌\33\[48;2;18;7;5m\33\[38;2;17;9;6m▗\33\[48;2;18;7;6m\33\[38;2;18;10;7m┓\33\[48;2;31;19;14m\33\[38;2;22;10;9m▊\33\[48;2;22;18;15m\33\[38;2;39;28;21m▌\33\[48;2;0;0;0m\33\[38;2;2;2;2m     \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m  \33\[38;2;100;92;89m▝\33\[48;2;100;89;85m\33\[38;2;36;34;34m▘\33\[48;2;60;44;44m\33\[38;2;72;54;55m▎\33\[48;2;62;46;46m\33\[38;2;48;34;34m▇\33\[48;2;60;42;42m\33\[38;2;50;36;36m▅\33\[48;2;48;34;34m\33\[38;2;57;41;41m▆\33\[48;2;59;42;42m\33\[38;2;71;54;54m┗\33\[48;2;60;41;42m\33\[38;2;57;38;38m▄\33\[48;2;54;34;36m\33\[38;2;61;41;42m▌\33\[48;2;52;33;34m\33\[38;2;0;0;0m \33\[48;2;86;73;74m\33\[38;2;57;37;39m▆\33\[48;2;52;27;25m\33\[38;2;52;29;31m▎\33\[48;2;56;30;29m\33\[38;2;0;0;0m \33\[48;2;74;42;43m\33\[38;2;96;57;55m▆\33\[48;2;84;45;44m\33\[38;2;110;69;66m╸\33\[48;2;123;74;70m\33\[38;2;87;47;48m▖\33\[48;2;144;96;91m\33\[38;2;160;113;107m▝\33\[48;2;165;116;112m\33\[38;2;136;91;90m▄\33\[48;2;168;117;113m\33\[38;2;111;71;72m▄\33\[48;2;177;124;119m\33\[38;2;101;61;63m▄\33\[48;2;186;132;127m\33\[38;2;95;50;51m▃\33\[48;2;191;136;130m\33\[38;2;124;67;63m▂\33\[48;2;203;143;137m\33\[38;2;163;102;93m▃\33\[48;2;205;142;134m\33\[38;2;177;112;100m▃\33\[48;2;207;142;131m\33\[38;2;189;124;112m▖\33\[48;2;223;163;152m\33\[38;2;217;153;142m▎\33\[48;2;221;158;149m\33\[38;2;206;139;127m▗\33\[48;2;211;145;134m\33\[38;2;197;129;116m▃\33\[48;2;208;145;134m\33\[38;2;179;115;104m▂\33\[48;2;204;140;130m\33\[38;2;164;100;90m▃\33\[48;2;187;124;115m\33\[38;2;120;63;57m▂\33\[48;2;178;115;106m\33\[38;2;103;52;51m▄\33\[48;2;164;105;96m\33\[38;2;85;41;42m▅\33\[48;2;145;93;87m\33\[38;2;82;43;43m▅\33\[48;2;93;56;56m\33\[38;2;113;69;68m▁\33\[48;2;75;44;45m\33\[38;2;114;74;72m▃\33\[48;2;62;33;35m\33\[38;2;112;69;65m▃\33\[48;2;64;33;34m\33\[38;2;97;55;49m▂\33\[48;2;60;34;35m\33\[38;2;0;0;0m \33\[48;2;48;22;21m\33\[38;2;53;28;28m▎\33\[48;2;45;23;18m\33\[38;2;40;18;14m━\33\[48;2;44;23;18m\33\[38;2;42;21;16m▄\33\[48;2;38;18;13m\33\[38;2;41;20;15m⎺\33\[48;2;44;23;19m\33\[38;2;71;57;57m▝\33\[48;2;63;49;48m\33\[38;2;43;23;21m▅\33\[48;2;40;21;17m\33\[38;2;63;47;47m▘\33\[48;2;45;28;27m\33\[38;2;56;42;42m┏\33\[48;2;30;14;14m\33\[38;2;41;25;23m▎\33\[48;2;26;12;11m\33\[38;2;21;7;7m▆\33\[48;2;26;12;12m\33\[38;2;21;8;8m▆\33\[48;2;26;13;11m\33\[38;2;23;10;9m▄\33\[48;2;33;19;18m\33\[38;2;24;10;10m▆\33\[48;2;37;23;21m\33\[38;2;27;13;12m▆\33\[48;2;26;12;11m\33\[38;2;21;6;6m▗\33\[48;2;25;13;11m\33\[38;2;24;10;9m▇\33\[48;2;28;15;14m\33\[38;2;77;67;63m╺\33\[48;2;25;13;11m\33\[38;2;32;18;13m╴\33\[48;2;26;15;12m\33\[38;2;34;22;17m▗\33\[48;2;44;34;27m\33\[38;2;28;21;18m▄\33\[48;2;0;0;0m\33\[38;2;3;3;2m     \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m   \33\[48;2;83;70;66m\33\[38;2;8;7;7m▎\33\[48;2;51;37;36m\33\[38;2;83;66;64m▃\33\[48;2;51;37;37m\33\[38;2;55;41;41m▄\33\[48;2;48;34;34m\33\[38;2;61;46;46m▄\33\[48;2;61;46;46m\33\[38;2;61;44;44m▄\33\[48;2;61;43;43m\33\[38;2;53;33;36m▁\33\[48;2;59;39;40m\33\[38;2;54;35;36m▄\33\[48;2;57;37;38m\33\[38;2;67;48;49m▘\33\[48;2;52;32;34m\33\[38;2;62;42;43m▘\33\[48;2;53;31;33m\33\[38;2;53;33;35m▄\33\[48;2;53;31;32m\33\[38;2;43;23;25m▃\33\[48;2;55;31;32m\33\[38;2;122;77;71m▗\33\[48;2;94;55;53m\33\[38;2;156;104;94m▄\33\[48;2;90;51;48m\33\[38;2;149;93;83m▄\33\[48;2;131;80;73m\33\[38;2;111;59;54m▗\33\[48;2;133;83;78m\33\[38;2;113;64;59m▅\33\[48;2;130;84;82m\33\[38;2;207;174;172m▂\33\[48;2;149;114;115m\33\[38;2;102;67;70m┳\33\[48;2;107;74;77m\33\[38;2;0;0;0m \33\[48;2;105;59;58m\33\[38;2;97;53;54m▄\33\[48;2;122;65;61m\33\[38;2;194;146;141m▂\33\[48;2;143;77;69m\33\[38;2;169;94;86m▄\33\[48;2;166;98;86m\33\[38;2;199;134;124m▄\33\[48;2;220;157;149m\33\[38;2;203;138;126m▌\33\[48;2;227;169;159m\33\[38;2;237;183;180m▅\33\[48;2;219;153;146m\33\[38;2;186;114;101m▝\33\[48;2;149;77;70m\33\[38;2;176;100;91m▌\33\[48;2;149;82;75m\33\[38;2;118;56;51m▇\33\[48;2;113;51;45m\33\[38;2;118;57;50m╴\33\[48;2;103;45;42m\33\[38;2;169;103;94m▃\33\[48;2;92;41;42m\33\[38;2;167;97;92m▅\33\[48;2;131;83;79m\33\[38;2;228;204;204m▃\33\[48;2;131;100;101m\33\[38;2;194;185;187m⎼\33\[48;2;99;68;69m\33\[38;2;0;0;0m \33\[48;2;128;85;81m\33\[38;2;77;41;41m▅\33\[48;2;124;76;71m\33\[38;2;95;56;56m▅\33\[48;2;116;69;62m\33\[38;2;68;33;32m▄\33\[48;2;94;51;47m\33\[38;2;118;66;60m▆\33\[48;2;76;39;36m\33\[38;2;143;82;69m▄\33\[48;2;63;31;28m\33\[38;2;132;74;60m▃\33\[48;2;49;23;19m\33\[38;2;84;43;37m▖\33\[48;2;40;15;11m\33\[38;2;49;21;17m▂\33\[48;2;45;22;16m\33\[38;2;46;20;15m▄\33\[48;2;38;16;13m\33\[38;2;47;22;18m▃\33\[48;2;45;26;23m\33\[38;2;49;28;27m▄\33\[48;2;34;16;17m\33\[38;2;54;37;37m▘\33\[48;2;19;5;5m\33\[38;2;0;0;0m \33\[48;2;16;2;3m\33\[38;2;19;5;5m▂\33\[48;2;19;5;5m\33\[38;2;26;12;11m▁\33\[48;2;22;8;8m\33\[38;2;0;0;0m \33\[48;2;24;9;9m\33\[38;2;34;17;15m▁\33\[48;2;29;15;13m\33\[38;2;0;0;0m \33\[48;2;72;64;60m\33\[38;2;37;22;19m▆\33\[48;2;35;20;18m\33\[38;2;0;0;0m \33\[48;2;31;17;15m\33\[38;2;55;41;35m▁\33\[48;2;35;21;19m\33\[38;2;28;21;18m▄\33\[48;2;0;0;0m\33\[38;2;67;54;48m⎻\33\[38;2;41;35;32m \33\[38;2;0;0;0m     \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m   \33\[48;2;13;12;12m\33\[38;2;110;98;93m▝\33\[48;2;89;72;71m\33\[38;2;0;0;0m \33\[48;2;74;56;55m\33\[38;2;101;84;77m▗\33\[48;2;68;51;51m\33\[38;2;87;69;63m▁\33\[48;2;58;41;41m\33\[38;2;74;56;56m▂\33\[48;2;57;38;39m\33\[38;2;48;30;30m▄\33\[48;2;63;44;45m\33\[38;2;53;35;36m▌\33\[48;2;50;31;32m\33\[38;2;0;0;0m \33\[48;2;44;25;26m\33\[38;2;53;33;34m▘\33\[38;2;31;16;16m▄\33\[48;2;49;29;30m\33\[38;2;34;18;19m▌\33\[48;2;158;109;100m\33\[38;2;76;45;45m▌\33\[48;2;177;121;108m\33\[38;2;195;138;124m▄\33\[48;2;177;118;104m\33\[38;2;207;148;132m▄\33\[48;2;153;94;84m\33\[38;2;197;132;117m▆\33\[48;2;139;82;75m\33\[38;2;198;133;118m▅\33\[48;2;218;179;174m\33\[38;2;200;138;128m▆\33\[48;2;158;121;121m\33\[38;2;204;151;146m▆\33\[48;2;114;69;72m\33\[38;2;198;139;138m▅\33\[48;2;139;88;86m\33\[38;2;188;116;115m▅\33\[48;2;211;170;166m\33\[38;2;183;110;109m▆\33\[48;2;201;137;136m\33\[38;2;206;140;137m▄\33\[48;2;214;151;143m\33\[38;2;222;159;154m▇\33\[48;2;232;171;169m\33\[38;2;227;164;158m▊\33\[48;2;238;180;181m\33\[38;2;242;189;189m┃\33\[48;2;216;142;137m\33\[38;2;230;161;160m▊\33\[48;2;146;71;67m\33\[38;2;191;114;109m▌\33\[48;2;111;49;45m\33\[38;2;122;56;54m▁\33\[48;2;140;69;61m\33\[38;2;126;62;55m▊\33\[48;2;180;112;103m\33\[38;2;153;82;73m▌\33\[48;2;198;130;124m\33\[38;2;213;151;151m▝\33\[48;2;245;226;227m\33\[38;2;207;149;147m▆\33\[48;2;190;130;128m\33\[38;2;222;197;200m▘\33\[48;2;107;60;60m\33\[38;2;191;120;117m▅\33\[48;2;104;58;54m\33\[38;2;174;103;98m▆\33\[48;2;136;80;78m\33\[38;2;157;85;79m▇\33\[48;2;109;55;48m\33\[38;2;168;102;89m▁\33\[48;2;150;90;77m\33\[38;2;105;57;51m▘\33\[48;2;167;103;87m\33\[38;2;155;91;77m▘\33\[48;2;137;77;62m\33\[38;2;156;92;76m▊\33\[48;2;88;45;38m\33\[38;2;116;63;52m▌\33\[48;2;53;22;17m\33\[38;2;63;29;25m▃\33\[48;2;51;22;17m\33\[38;2;54;24;20m▖\33\[48;2;56;34;35m\33\[38;2;52;24;21m▊\33\[48;2;73;54;56m\33\[38;2;0;0;0m \33\[48;2;57;38;38m\33\[38;2;92;75;76m╸\33\[48;2;33;17;15m\33\[38;2;99;75;74m▄\33\[48;2;51;32;29m\33\[38;2;105;81;78m▖\33\[48;2;39;20;16m\33\[38;2;54;33;30m▄\33\[48;2;40;21;18m\33\[38;2;49;29;25m▆\33\[48;2;43;24;20m\33\[38;2;51;32;29m▗\33\[48;2;37;19;16m\33\[38;2;45;26;23m▎\33\[48;2;35;18;15m\33\[38;2;29;13;10m▊\33\[48;2;44;27;22m\33\[38;2;72;57;49m▗\33\[48;2;14;11;9m\33\[38;2;52;37;31m▌\33\[48;2;0;0;0m\33\[38;2;0;0;0m        \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m    \33\[48;2;93;80;76m\33\[38;2;22;21;20m▖\33\[48;2;107;89;81m\33\[38;2;81;62;58m▌\33\[48;2;109;90;80m\33\[38;2;140;125;114m▁\33\[48;2;67;48;44m\33\[38;2;121;106;99m▃\33\[48;2;69;51;49m\33\[38;2;90;75;70m▃\33\[48;2;56;39;39m\33\[38;2;0;0;0m \33\[48;2;59;40;41m\33\[38;2;86;68;68m▌\33\[48;2;58;39;40m\33\[38;2;0;0;0m \33\[48;2;48;29;31m\33\[38;2;75;55;56m▖\33\[48;2;52;31;32m\33\[38;2;40;22;23m▌\33\[48;2;167;121;114m\33\[38;2;68;40;39m▎\33\[48;2;215;153;142m\33\[38;2;196;140;128m▌\33\[48;2;222;158;148m\33\[38;2;230;163;155m▅\33\[48;2;222;156;146m\33\[38;2;231;164;156m▆\33\[48;2;220;152;140m\33\[38;2;231;162;155m▄\33\[48;2;209;145;134m\33\[38;2;229;161;153m▄\33\[48;2;220;154;147m\33\[38;2;192;122;114m⎻\33\[48;2;200;134;127m\33\[38;2;229;162;154m▄\33\[48;2;195;126;121m\33\[38;2;231;167;161m▄\33\[48;2;200;131;125m\33\[38;2;233;171;165m▅\33\[48;2;234;170;168m\33\[38;2;223;158;154m▘\33\[48;2;232;167;163m\33\[38;2;231;162;160m▅\33\[48;2;232;160;161m\33\[38;2;238;171;171m▝\33\[48;2;237;168;169m\33\[38;2;233;158;162m▁\33\[48;2;211;124;120m\33\[38;2;228;148;145m▌\33\[48;2;152;70;66m\33\[38;2;184;98;93m▌\33\[48;2;128;59;57m\33\[38;2;123;57;54m┗\33\[48;2;156;80;73m\33\[38;2;134;65;61m▎\33\[48;2;168;89;80m\33\[38;2;184;108;97m▗\33\[48;2;193;120;110m\33\[38;2;196;123;112m▄\33\[48;2;205;135;124m\33\[38;2;202;131;120m▌\33\[48;2;199;126;118m\33\[38;2;209;139;128m▄\33\[48;2;188;114;109m\33\[38;2;212;141;131m▄\33\[48;2;179;105;98m\33\[38;2;216;145;135m▄\33\[48;2;173;101;93m\33\[38;2;216;146;138m▅\33\[48;2;184;121;106m\33\[38;2;211;143;135m▆\33\[48;2;185;117;103m\33\[38;2;203;133;125m▆\33\[48;2;173;103;88m\33\[38;2;183;113;101m▌\33\[48;2;160;91;75m\33\[38;2;140;68;59m▗\33\[48;2;87;42;36m\33\[38;2;119;60;51m▌\33\[48;2;66;31;28m\33\[38;2;73;36;32m▂\33\[48;2;58;26;24m\33\[38;2;62;32;29m┏\33\[48;2;40;14;13m\33\[38;2;50;20;18m▌\33\[48;2;45;23;22m\33\[38;2;36;17;12m▂\33\[48;2;65;46;46m\33\[38;2;46;26;25m▄\33\[48;2;96;70;70m\33\[38;2;43;23;20m▅\33\[48;2;51;31;26m\33\[38;2;0;0;0m \33\[48;2;39;19;14m\33\[38;2;43;24;18m▄\33\[48;2;34;16;10m\33\[38;2;41;22;16m▘\33\[48;2;41;22;17m\33\[38;2;67;49;48m▁\33\[48;2;42;23;19m\33\[38;2;55;37;35m▃\33\[48;2;48;30;27m\33\[38;2;61;44;42m╹\33\[48;2;51;34;27m\33\[38;2;0;0;0m \33\[48;2;16;13;12m\33\[38;2;44;33;28m▊\33\[48;2;0;0;0m\33\[38;2;1;0;0m━\33\[38;2;12;11;12m╶\33\[38;2;0;0;0m      \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m    \33\[38;2;130;118;111m▝\33\[48;2;133;122;114m\33\[38;2;15;14;13m▂\33\[48;2;106;98;91m\33\[38;2;51;49;46m▗\33\[48;2;71;65;62m\33\[38;2;101;85;78m▆\33\[48;2;75;57;53m\33\[38;2;93;79;77m╶\33\[48;2;66;49;49m\33\[38;2;94;78;77m╏\33\[48;2;52;32;33m\33\[38;2;60;40;41m▄\33\[48;2;52;33;34m\33\[38;2;47;27;28m▄\33\[48;2;52;32;33m\33\[38;2;78;59;60m╴\33\[38;2;51;31;32m▄\33\[48;2;170;119;111m\33\[38;2;75;45;42m▌\33\[48;2;219;153;144m\33\[38;2;201;139;128m▌\33\[48;2;232;166;159m\33\[38;2;228;159;151m▌\33\[48;2;236;172;167m\33\[38;2;234;168;163m▄\33\[48;2;235;169;165m\33\[38;2;237;176;172m▗\33\[48;2;229;160;153m\33\[38;2;236;170;165m▆\33\[48;2;233;167;162m\33\[38;2;239;174;172m▂\33\[48;2;232;170;164m\33\[38;2;239;176;173m▂\33\[38;2;234;171;167m▄\33\[48;2;231;168;163m\33\[38;2;240;184;179m━\33\[48;2;233;168;164m\33\[38;2;231;160;159m▄\33\[48;2;231;158;156m\33\[38;2;0;0;0m \33\[48;2;233;158;160m \33\[48;2;231;149;154m\33\[38;2;233;157;160m┛\33\[48;2;204;115;114m\33\[38;2;220;133;135m▌\33\[48;2;146;62;59m\33\[38;2;179;89;86m▌\33\[48;2;130;57;56m\33\[38;2;121;50;47m▗\33\[48;2;158;81;75m\33\[38;2;127;53;50m▖\33\[48;2;185;108;99m\33\[38;2;167;85;78m▃\33\[48;2;195;120;108m\33\[38;2;206;135;122m▅\33\[48;2;206;136;124m\33\[38;2;222;152;144m▃\33\[48;2;211;141;131m\33\[38;2;225;156;148m▂\33\[48;2;220;149;140m\33\[38;2;223;147;140m▄\33\[48;2;225;155;147m\33\[38;2;225;152;145m▃\33\[48;2;224;154;147m\33\[38;2;222;147;141m▃\33\[48;2;212;136;130m\33\[38;2;220;146;140m▊\33\[48;2;197;116;109m\33\[38;2;207;129;123m▌\33\[48;2;165;84;76m\33\[38;2;183;101;93m▌\33\[48;2;152;79;68m\33\[38;2;136;65;59m▅\33\[48;2;90;39;35m\33\[38;2;115;55;50m▖\33\[48;2;73;37;34m\33\[38;2;83;40;35m▌\33\[48;2;61;31;30m\33\[38;2;65;34;31m▊\33\[48;2;38;13;12m\33\[38;2;52;25;23m▌\33\[48;2;36;15;11m\33\[38;2;39;18;15m▗\33\[48;2;37;16;13m\33\[38;2;0;0;0m \33\[48;2;42;22;16m\33\[38;2;37;17;13m▄\33\[48;2;41;21;16m\33\[38;2;38;20;14m▄\33\[48;2;42;23;17m\33\[38;2;35;17;12m▆\33\[48;2;33;15;11m\33\[38;2;48;30;27m▝\33\[48;2;79;62;60m\33\[38;2;40;21;19m▅\33\[48;2;40;22;18m\33\[38;2;63;44;41m▘\33\[48;2;58;41;36m\33\[38;2;0;0;0m \33\[48;2;78;64;56m\33\[38;2;33;25;21m▅\33\[48;2;0;0;0m\33\[38;2;51;43;37m \33\[38;2;0;0;0m        \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m      \33\[38;2;96;89;83m \33\[48;2;80;66;60m\33\[38;2;0;0;0m▖\33\[48;2;84;66;59m\33\[38;2;113;99;92m▆\33\[48;2;72;53;50m\33\[38;2;114;99;91m▖\33\[48;2;78;58;57m\33\[38;2;101;82;76m▁\33\[48;2;64;45;45m\33\[38;2;114;100;91m▃\33\[48;2;47;33;32m\33\[38;2;67;48;45m─\33\[48;2;55;35;35m\33\[38;2;120;100;91m▃\33\[48;2;153;105;98m\33\[38;2;86;55;52m▊\33\[48;2;217;155;147m\33\[38;2;203;149;142m▎\33\[48;2;228;158;151m\33\[38;2;231;165;158m┏\33\[48;2;236;171;166m\33\[38;2;231;163;158m▎\33\[48;2;238;175;171m\33\[38;2;231;159;154m▂\33\[48;2;235;168;164m\33\[38;2;213;131;126m▂\33\[48;2;226;151;146m\33\[38;2;187;97;89m▃\33\[48;2;212;135;127m\33\[38;2;213;136;128m▄\33\[48;2;228;159;154m\33\[38;2;220;148;141m▘\33\[48;2;226;143;148m\33\[38;2;225;147;150m▊\33\[48;2;227;145;148m\33\[38;2;226;143;148m▎\33\[48;2;227;149;149m\33\[38;2;226;147;147m▄\33\[48;2;232;154;158m\33\[38;2;236;166;174m▂\33\[48;2;224;136;141m\33\[38;2;231;151;158m▎\33\[48;2;184;93;92m\33\[38;2;203;112;113m▌\33\[48;2;147;61;60m\33\[38;2;169;78;76m▎\33\[48;2;131;53;52m\33\[38;2;119;45;45m┗\33\[48;2;172;87;83m\33\[38;2;123;48;46m▘\33\[48;2;175;89;83m\33\[38;2;191;103;97m┓\33\[48;2;154;75;71m\33\[38;2;129;52;51m┏\33\[48;2;186;113;104m\33\[38;2;120;53;52m▖\33\[48;2;219;149;140m\33\[38;2;185;111;100m▅\33\[48;2;223;151;143m\33\[38;2;192;120;111m▃\33\[48;2;224;150;143m\33\[38;2;211;137;130m▁\33\[48;2;213;131;126m\33\[38;2;218;138;134m▌\33\[48;2;208;124;119m\33\[38;2;217;139;134m▘\33\[48;2;201;115;108m\33\[38;2;194;107;100m▄\33\[48;2;167;84;77m\33\[38;2;184;100;93m▌\33\[48;2;118;54;49m\33\[38;2;141;65;60m▌\33\[48;2;108;53;48m\33\[38;2;102;45;40m▌\33\[48;2;77;37;33m\33\[38;2;103;52;47m▖\33\[48;2;62;31;29m\33\[38;2;60;30;28m▄\33\[48;2;42;17;13m\33\[38;2;53;23;22m▎\33\[48;2;39;18;13m\33\[38;2;47;24;19m▗\33\[48;2;33;10;8m\33\[38;2;49;25;22m▄\33\[48;2;37;16;12m\33\[38;2;48;22;20m▄\33\[48;2;34;15;13m\33\[38;2;26;9;9m▝\33\[48;2;31;14;13m\33\[38;2;40;21;20m▁\33\[48;2;33;15;15m\33\[38;2;39;20;18m▂\33\[48;2;41;21;18m\33\[38;2;0;0;0m \33\[48;2;45;27;24m \33\[48;2;66;52;46m\33\[38;2;49;31;25m▆\33\[48;2;13;10;8m\33\[38;2;72;59;51m▄\33\[48;2;0;0;0m\33\[38;2;109;101;92m \33\[38;2;0;0;0m        \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m       \33\[38;2;129;123;116m \33\[48;2;105;92;85m\33\[38;2;0;0;0m \33\[48;2;111;92;82m\33\[38;2;133;115;105m▎\33\[48;2;87;78;71m\33\[38;2;74;67;62m▄\33\[48;2;108;92;80m\33\[38;2;147;129;114m▅\33\[48;2;67;59;53m\33\[38;2;141;124;112m▆\33\[48;2;124;103;93m\33\[38;2;102;78;70m▅\33\[48;2;140;104;97m\33\[38;2;120;80;73m▆\33\[48;2;211;152;144m\33\[38;2;189;137;130m▎\33\[48;2;224;154;147m\33\[38;2;208;142;131m▄\33\[48;2;227;153;147m\33\[38;2;210;140;131m▃\33\[48;2;214;136;130m\33\[38;2;198;120;112m▃\33\[48;2;189;103;96m\33\[38;2;192;116;107m▄\33\[48;2;197;114;107m\33\[38;2;198;135;129m▆\33\[48;2;221;154;148m\33\[38;2;206;151;145m▄\33\[48;2;224;161;157m\33\[38;2;211;159;158m▃\33\[48;2;219;155;155m\33\[38;2;222;146;148m┗\33\[48;2;227;148;151m\33\[38;2;209;147;148m▃\33\[48;2;227;150;152m\33\[38;2;211;147;147m▁\33\[48;2;232;156;161m\33\[38;2;247;199;209m▝\33\[48;2;227;144;150m\33\[38;2;240;182;191m▘\33\[48;2;193;99;99m\33\[38;2;210;118;121m▌\33\[48;2;141;58;56m\33\[38;2;165;74;72m▊\33\[48;2;132;55;54m\33\[38;2;97;40;41m▁\33\[48;2;149;70;67m\33\[38;2;75;29;32m▃\33\[48;2;160;77;74m\33\[38;2;71;28;31m▄\33\[48;2;101;38;39m\33\[38;2;89;40;40m▄\33\[48;2;126;64;57m\33\[38;2;98;38;37m▘\33\[48;2;150;83;74m\33\[38;2;173;99;89m▝\33\[48;2;179;110;101m\33\[38;2;161;99;92m▂\33\[48;2;193;124;115m\33\[38;2;173;109;101m▃\33\[48;2;201;126;119m\33\[38;2;177;114;102m▁\33\[48;2;205;122;115m\33\[38;2;196;117;108m▄\33\[48;2;187;103;97m\33\[38;2;170;84;77m▗\33\[48;2;161;78;73m\33\[38;2;142;65;60m▂\33\[48;2;105;48;43m\33\[38;2;129;60;55m▌\33\[48;2;93;42;37m\33\[38;2;89;39;34m┣\33\[48;2;77;36;33m\33\[38;2;97;47;42m▌\33\[48;2;59;31;29m\33\[38;2;64;32;29m▎\33\[48;2;48;22;19m\33\[38;2;32;10;11m▁\33\[48;2;49;24;20m\33\[38;2;60;30;32m▁\33\[48;2;54;25;22m\33\[38;2;75;37;38m▁\33\[48;2;52;23;23m\33\[38;2;74;36;36m▖\33\[48;2;31;13;11m\33\[38;2;23;6;6m▅\33\[48;2;36;19;18m\33\[38;2;28;14;13m▇\33\[48;2;34;18;16m\33\[38;2;26;12;11m▅\33\[48;2;38;23;21m\33\[38;2;0;0;0m \33\[48;2;64;49;42m \33\[48;2;57;39;33m\33\[38;2;122;110;99m▅\33\[48;2;70;56;47m\33\[38;2;28;24;21m▗\33\[48;2;61;57;53m\33\[38;2;71;57;49m▊\33\[48;2;0;0;0m\33\[38;2;19;18;17m \33\[38;2;0;0;0m       \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m        \33\[38;2;124;114;108m \33\[48;2;105;91;84m\33\[38;2;1;1;1m▄\33\[48;2;126;112;102m\33\[38;2;16;15;14m▂\33\[48;2;110;99;89m\33\[38;2;35;32;30m▂\33\[48;2;139;121;108m\33\[38;2;113;95;84m▄\33\[48;2;135;118;110m\33\[38;2;83;63;56m▄\33\[48;2;72;49;46m\33\[38;2;0;0;0m \33\[48;2;210;158;150m\33\[38;2;141;102;100m▎\33\[48;2;205;138;126m\33\[38;2;225;167;158m▖\33\[48;2;205;138;125m\33\[38;2;207;143;131m▁\33\[48;2;185;108;99m\33\[38;2;200;128;118m▊\33\[48;2;185;125;118m\33\[38;2;177;103;95m▌\33\[48;2;192;140;133m\33\[38;2;186;133;125m▊\33\[48;2;198;146;141m\33\[38;2;212;156;150m▄\33\[48;2;210;160;160m\33\[38;2;213;155;153m▆\33\[48;2;213;157;158m\33\[38;2;221;158;155m▃\33\[48;2;212;155;153m\33\[38;2;224;160;158m▂\33\[48;2;206;149;149m\33\[38;2;224;160;159m▂\33\[48;2;209;137;139m\33\[38;2;219;160;160m▄\33\[48;2;197;116;120m\33\[38;2;209;145;146m▃\33\[48;2;176;94;94m\33\[38;2;204;138;139m▂\33\[48;2;116;49;52m\33\[38;2;183;112;109m▂\33\[48;2;75;30;33m\33\[38;2;165;89;87m▂\33\[48;2;75;34;36m\33\[38;2;151;74;72m▃\33\[48;2;98;48;47m\33\[38;2;150;74;70m▄\33\[48;2;124;62;57m\33\[38;2;148;74;67m▄\33\[48;2;134;68;60m\33\[38;2;146;74;66m▃\33\[48;2;145;78;69m\33\[38;2;139;71;63m▆\33\[48;2;148;81;72m\33\[38;2;140;72;64m▄\33\[48;2;157;92;84m\33\[38;2;144;81;75m▄\33\[48;2;167;104;94m\33\[38;2;151;92;82m▆\33\[48;2;182;111;99m\33\[38;2;171;109;97m▖\33\[48;2;158;77;69m\33\[38;2;175;97;86m▌\33\[48;2;139;66;59m\33\[38;2;154;81;73m▂\33\[48;2;112;54;48m\33\[38;2;0;0;0m \33\[48;2;110;54;48m\33\[38;2;151;86;73m▅\33\[48;2;86;44;39m\33\[38;2;121;62;54m▎\33\[48;2;35;14;14m\33\[38;2;60;31;29m▊\33\[48;2;19;4;6m\33\[38;2;0;0;0m \33\[48;2;57;28;32m\33\[38;2;21;7;9m▆\33\[48;2;74;38;39m\33\[38;2;19;5;6m▅\33\[48;2;26;9;9m\33\[38;2;0;0;0m \33\[48;2;19;5;6m\33\[38;2;26;12;12m▂\33\[48;2;30;16;15m\33\[38;2;0;0;0m \33\[48;2;34;19;18m\33\[38;2;45;34;30m▁\33\[48;2;41;28;25m\33\[38;2;87;76;68m▝\33\[48;2;57;42;35m\33\[38;2;93;81;72m▘\33\[48;2;112;99;90m\33\[38;2;64;48;40m▆\33\[48;2;58;48;42m\33\[38;2;10;9;7m▁\33\[48;2;18;16;15m\33\[38;2;72;62;55m┛\33\[48;2;0;0;0m\33\[38;2;0;0;0m        \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m            \33\[48;2;90;79;72m\33\[38;2;7;6;6m▄\33\[48;2;76;57;49m\33\[38;2;77;68;64m▄\33\[48;2;66;45;43m\33\[38;2;0;0;0m \33\[48;2;192;149;144m\33\[38;2;88;60;61m▎\33\[48;2;219;162;152m\33\[38;2;212;151;141m▝\33\[48;2;213;153;141m\33\[38;2;227;171;158m▖\33\[48;2;207;148;136m\33\[38;2;193;128;118m▝\33\[48;2;172;114;105m\33\[38;2;192;135;122m▖\33\[48;2;178;127;120m\33\[38;2;211;163;157m▗\33\[48;2;205;148;145m\33\[38;2;173;106;106m▝\33\[48;2;188;111;116m\33\[38;2;132;53;61m━\33\[48;2;182;112;118m\33\[38;2;116;52;59m┓\33\[48;2;202;129;136m\33\[38;2;233;212;209m▂\33\[48;2;206;137;144m\33\[38;2;237;215;210m▁\33\[48;2;233;169;172m\33\[38;2;205;137;145m▇\33\[48;2;229;163;167m\33\[38;2;199;131;138m▅\33\[48;2;223;151;155m\33\[38;2;183;103;108m▄\33\[48;2;219;145;147m\33\[38;2;177;97;99m▅\33\[48;2;194;112;109m\33\[38;2;166;82;84m▆\33\[48;2;162;77;77m\33\[38;2;208;174;168m▁\33\[48;2;146;71;69m\33\[38;2;187;152;141m▁\33\[48;2;131;63;59m\33\[38;2;159;126;118m▃\33\[48;2;118;58;54m\33\[38;2;142;103;96m▄\33\[48;2;109;55;53m\33\[38;2;142;97;91m▖\33\[48;2;97;37;38m\33\[38;2;136;65;63m▄\33\[48;2;156;86;80m\33\[38;2;127;58;58m▘\33\[48;2;160;101;90m\33\[38;2;178;125;112m▗\33\[48;2;185;128;116m\33\[38;2;0;0;0m \33\[48;2;161;93;83m\33\[38;2;198;145;134m▗\33\[48;2;166;103;92m\33\[38;2;147;82;73m▄\33\[48;2;173;111;98m\33\[38;2;119;55;49m▘\33\[48;2;133;72;61m\33\[38;2;166;100;84m▊\33\[48;2;83;46;41m\33\[38;2;108;57;48m▎\33\[48;2;23;7;6m\33\[38;2;60;31;30m▌\33\[48;2;17;4;5m\33\[38;2;19;5;6m▎\33\[48;2;17;6;6m\33\[38;2;20;7;7m┛\33\[48;2;17;5;6m\33\[38;2;18;7;7m▄\33\[48;2;23;10;9m\33\[38;2;36;22;19m▗\33\[48;2;39;25;20m\33\[38;2;0;0;0m \33\[48;2;52;40;35m\33\[38;2;37;21;18m▘\33\[48;2;15;12;10m\33\[38;2;0;0;0m \33\[48;2;18;14;12m\33\[38;2;60;45;38m▗\33\[48;2;65;53;45m\33\[38;2;8;6;5m▆\33\[48;2;71;56;48m\33\[38;2;0;0;0m▇\33\[48;2;0;0;0m          \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m             \33\[38;2;29;24;23m \33\[48;2;157;148;145m\33\[38;2;0;0;0m▅\33\[48;2;96;75;74m\33\[38;2;86;75;73m▄\33\[48;2;191;145;138m\33\[38;2;105;78;75m▂\33\[48;2;216;161;150m\33\[38;2;0;0;0m \33\[48;2;209;152;138m\33\[38;2;215;161;147m▌\33\[48;2;200;145;131m\33\[38;2;0;0;0m \33\[48;2;206;156;149m\33\[38;2;196;145;133m▊\33\[48;2;219;165;160m\33\[38;2;212;162;156m▌\33\[48;2;216;142;147m\33\[38;2;224;167;163m▆\33\[48;2;205;122;132m\33\[38;2;218;155;154m▂\33\[48;2;214;182;179m\33\[38;2;207;125;135m▇\33\[48;2;235;207;204m\33\[38;2;219;130;144m▅\33\[48;2;234;207;204m\33\[38;2;228;146;158m▅\33\[48;2;245;227;223m\33\[38;2;225;144;161m▅\33\[48;2;215;145;155m\33\[38;2;227;195;192m▘\33\[48;2;236;211;207m\33\[38;2;220;136;149m▄\33\[48;2;209;128;137m\33\[38;2;220;182;178m▘\33\[48;2;219;192;188m\33\[38;2;198;99;109m▅\33\[48;2;176;139;128m\33\[38;2;177;77;81m▆\33\[48;2;158;75;73m\33\[38;2;0;0;0m \33\[48;2;142;70;69m\33\[38;2;155;72;68m▇\33\[48;2;155;74;69m\33\[38;2;158;85;78m▅\33\[48;2;159;83;76m\33\[38;2;165;98;89m▆\33\[48;2;169;105;96m\33\[38;2;165;99;90m▊\33\[48;2;171;112;103m\33\[38;2;0;0;0m \33\[48;2;167;109;98m\33\[38;2;148;88;80m▄\33\[48;2;149;83;74m\33\[38;2;192;132;120m▘\33\[48;2;173;111;100m\33\[38;2;149;79;71m▘\33\[48;2;160;96;84m\33\[38;2;116;62;57m▗\33\[48;2;89;47;46m\33\[38;2;132;72;64m▘\33\[48;2;72;38;37m\33\[38;2;0;0;0m \33\[48;2;25;8;8m \33\[48;2;20;5;6m\33\[38;2;21;7;7m▂\33\[48;2;20;6;6m\33\[38;2;0;0;0m \33\[48;2;19;6;6m\33\[38;2;21;7;7m▃\33\[48;2;26;14;13m\33\[38;2;0;0;0m \33\[48;2;36;21;16m\33\[38;2;73;62;56m▘\33\[48;2;44;32;27m\33\[38;2;35;19;13m▁\33\[48;2;33;26;21m\33\[38;2;39;24;18m▄\33\[48;2;47;33;29m\33\[38;2;4;3;2m▁\33\[48;2;0;0;0m\33\[38;2;48;42;37m \33\[38;2;0;0;0m           \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m               \33\[38;2;101;90;86m \33\[48;2;99;78;78m\33\[38;2;112;99;97m▌\33\[48;2;156;119;115m\33\[38;2;74;52;53m▄\33\[48;2;185;139;129m\33\[38;2;0;0;0m \33\[48;2;201;144;131m\33\[38;2;192;139;128m▖\33\[48;2;197;147;136m\33\[38;2;197;143;130m▊\33\[48;2;211;160;154m\33\[38;2;200;150;142m▊\33\[48;2;221;169;163m\33\[38;2;213;162;155m▅\33\[48;2;217;166;159m\33\[38;2;0;0;0m \33\[48;2;213;138;142m\33\[38;2;220;163;156m▆\33\[48;2;223;142;153m\33\[38;2;220;157;153m▄\33\[48;2;234;159;172m\33\[38;2;217;152;153m▅\33\[48;2;234;156;172m\33\[38;2;210;141;148m▆\33\[48;2;227;147;161m\33\[38;2;202;143;144m▄\33\[48;2;221;141;153m\33\[38;2;193;134;133m▄\33\[48;2;201;135;135m\33\[38;2;207;121;130m▝\33\[48;2;187;106;107m\33\[38;2;188;127;122m▖\33\[48;2;169;97;88m\33\[38;2;179;93;92m▘\33\[48;2;157;80;74m\33\[38;2;171;95;84m▂\33\[48;2;155;78;73m\33\[38;2;165;87;78m▃\33\[48;2;160;88;80m\33\[38;2;165;95;86m┏\33\[48;2;161;90;83m\33\[38;2;161;89;82m▄\33\[48;2;161;96;87m\33\[38;2;127;72;67m▗\33\[48;2;89;45;43m\33\[38;2;145;83;75m▘\33\[48;2;130;81;71m\33\[38;2;103;58;54m▌\33\[48;2;159;102;92m\33\[38;2;115;67;61m▁\33\[48;2;151;88;79m\33\[38;2;96;51;48m▅\33\[48;2;87;46;45m\33\[38;2;0;0;0m \33\[48;2;67;36;36m \33\[48;2;11;4;3m\33\[38;2;57;29;29m▘\33\[48;2;21;6;6m\33\[38;2;30;8;6m▎\33\[48;2;21;7;7m\33\[38;2;23;10;9m▁\33\[48;2;22;8;7m\33\[38;2;28;14;12m▁\33\[48;2;27;13;12m\33\[38;2;41;24;20m▁\33\[48;2;43;30;26m\33\[38;2;51;41;35m▄\33\[48;2;71;58;50m\33\[38;2;3;2;1m▂\33\[48;2;44;36;31m\33\[38;2;1;0;0m▄\33\[48;2;0;0;0m\33\[38;2;37;29;24m \33\[38;2;0;0;0m             \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m                \33\[48;2;83;66;66m\33\[38;2;38;34;33m▎\33\[48;2;74;54;56m\33\[38;2;89;69;70m▖\33\[48;2;77;50;50m\33\[38;2;0;0;0m \33\[48;2;169;124;114m\33\[38;2;59;44;40m▂\33\[48;2;192;140;128m\33\[38;2;0;0;0m \33\[48;2;195;147;138m\33\[38;2;201;151;143m▌\33\[48;2;210;160;152m\33\[38;2;192;149;141m▂\33\[48;2;212;159;152m\33\[38;2;206;161;154m▁\33\[48;2;223;161;155m\33\[38;2;216;159;153m▎\33\[48;2;216;154;148m\33\[38;2;223;159;153m▆\33\[48;2;207;147;143m\33\[38;2;219;155;151m▇\33\[48;2;215;153;151m\33\[38;2;204;142;140m┗\33\[48;2;211;152;151m\33\[38;2;197;135;135m━\33\[48;2;191;129;127m\33\[38;2;208;147;144m▃\33\[48;2;186;123;120m\33\[38;2;193;126;122m▄\33\[48;2;185;118;113m\33\[38;2;187;120;115m▄\33\[48;2;181;110;102m\33\[38;2;191;124;114m▅\33\[48;2;183;107;95m\33\[38;2;189;119;108m▅\33\[48;2;169;92;82m\33\[38;2;168;95;86m▄\33\[48;2;164;90;82m\33\[38;2;159;89;81m▄\33\[48;2;126;69;65m\33\[38;2;149;81;75m▌\33\[48;2;82;44;43m\33\[38;2;125;69;64m▘\33\[48;2;88;53;50m\33\[38;2;73;39;38m▊\33\[48;2;112;68;63m\33\[38;2;87;50;48m▅\33\[48;2;80;44;42m\33\[38;2;0;0;0m \33\[48;2;69;38;36m \33\[48;2;71;39;37m\33\[38;2;9;5;4m▄\33\[48;2;0;0;0m\33\[38;2;71;38;38m \33\[48;2;2;0;0m\33\[38;2;0;0;0m▌\33\[48;2;46;30;27m\33\[38;2;35;15;12m▊\33\[48;2;45;30;27m\33\[38;2;79;71;69m▁\33\[48;2;41;26;23m\33\[38;2;62;49;45m▆\33\[48;2;11;7;6m\33\[38;2;64;48;43m▘\33\[48;2;0;0;0m\33\[38;2;5;2;2m \33\[38;2;0;0;0m                \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m                \33\[38;2;122;106;102m \33\[48;2;155;145;140m\33\[38;2;0;0;0m▅\33\[48;2;114;95;88m▅\33\[48;2;0;0;0m\33\[38;2;47;36;33m▘\33\[38;2;188;139;127m \33\[48;2;164;125;115m\33\[38;2;19;14;13m▃\33\[48;2;176;135;126m\33\[38;2;0;0;0m \33\[48;2;201;159;153m\33\[38;2;187;146;138m▂\33\[48;2;215;163;157m\33\[38;2;200;155;151m▄\33\[48;2;217;164;158m\33\[38;2;206;160;155m▃\33\[48;2;216;156;152m\33\[38;2;217;165;161m▅\33\[48;2;218;162;160m\33\[38;2;220;169;168m▗\33\[48;2;221;167;167m\33\[38;2;207;158;157m▂\33\[48;2;210;159;156m\33\[38;2;204;146;140m▝\33\[48;2;188;127;122m\33\[38;2;198;139;134m▊\33\[48;2;182;119;113m\33\[38;2;182;121;116m▄\33\[48;2;181;118;110m\33\[38;2;170;113;105m▄\33\[48;2;164;110;103m\33\[38;2;175;115;106m▘\33\[48;2;157;98;89m\33\[38;2;128;77;71m▗\33\[48;2;142;81;74m\33\[38;2;108;66;62m▄\33\[48;2;79;45;44m\33\[38;2;119;68;63m▘\33\[48;2;67;36;39m\33\[38;2;68;38;38m▝\33\[48;2;69;38;39m\33\[38;2;0;0;0m \33\[48;2;66;36;36m\33\[38;2;12;6;6m▂\33\[48;2;74;44;40m\33\[38;2;0;0;0m▅\33\[48;2;0;0;0m\33\[38;2;44;23;22m \33\[38;2;0;0;0m  \33\[38;2;37;18;15m \33\[38;2;83;75;74m \33\[38;2;58;56;53m \33\[38;2;0;0;0m                   \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m                   \33\[38;2;7;6;6m \33\[38;2;0;0;0m  \33\[38;2;176;137;129m \33\[48;2;142;109;103m\33\[38;2;20;15;14m▃\33\[48;2;168;132;125m\33\[38;2;0;0;0m \33\[48;2;194;152;145m\33\[38;2;169;132;123m▂\33\[48;2;205;155;151m\33\[38;2;185;144;136m▄\33\[48;2;210;158;155m\33\[38;2;189;146;137m▅\33\[48;2;200;149;143m\33\[38;2;195;148;139m▄\33\[48;2;204;152;146m\33\[38;2;179;131;121m▂\33\[48;2;193;135;129m\33\[38;2;161;114;104m▂\33\[48;2;175;115;107m\33\[38;2;151;103;93m▂\33\[48;2;165;110;100m\33\[38;2;143;96;86m▃\33\[48;2;146;96;87m\33\[38;2;113;69;61m▂\33\[48;2;116;71;65m\33\[38;2;86;49;47m▃\33\[48;2;78;42;42m\33\[38;2;17;8;8m▁\33\[48;2;67;36;37m\33\[38;2;7;3;3m▃\33\[48;2;72;40;42m\33\[38;2;0;0;0m▅\33\[48;2;0;0;0m\33\[38;2;68;37;38m \33\[38;2;0;0;0m                           \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m                        \33\[38;2;123;92;88m \33\[48;2;158;117;108m\33\[38;2;0;0;0m▅\33\[48;2;144;103;96m\33\[38;2;9;6;5m▄\33\[48;2;134;95;90m\33\[38;2;5;3;3m▂\33\[48;2;140;97;91m\33\[38;2;20;12;11m▂\33\[48;2;134;92;86m\33\[38;2;18;11;10m▂\33\[48;2;124;82;78m\33\[38;2;14;7;7m▂\33\[48;2;111;71;68m\33\[38;2;9;4;4m▃\33\[48;2;111;68;63m\33\[38;2;11;5;5m▅\33\[48;2;108;65;59m\33\[38;2;0;0;0m▆\33\[48;2;0;0;0m\33\[38;2;77;41;40m \33\[38;2;4;1;1m \33\[38;2;0;0;0m                              \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;0;0;0m                                                                  \33\[0m', nl,
'\33\[48;2;0;0;0m\33\[38;2;255;255;255m  _______          _______      _____           _       __   ___  \33\[0m', nl, 
'\33\[48;2;0;0;0m\33\[38;2;255;255;255m / ____\\ \\        / /_   _|    |  __ \\         | |     /_ | / _ \\ \33\[0m', nl, 
'\33\[48;2;0;0;0m\33\[38;2;255;255;255m| (___  \\ \\  /\\  / /  | |______| |__) |___  ___| |__    | || | | |\33\[0m', nl, 
'\33\[48;2;0;0;0m\33\[38;2;255;255;255m \\___ \\  \\ \\/  \\/ /   | |______|  _  // _ \\/ __| |_ \\   | || | | |\33\[0m', nl, 
'\33\[48;2;0;0;0m\33\[38;2;255;255;255m ____) |  \\  /\\  /   _| |_     | | \\ \\ (_) \\__ \\ | | |  | || |_| |\33\[0m', nl, 
'\33\[48;2;0;0;0m\33\[38;2;255;255;255m|_____/    \\/  \\/   |_____|    |_|  \\_\\___/|___/_| |_|  |_(_)___/ \33\[0m', nl, 
'\33\[48;2;0;0;0m\33\[38;2;255;255;255m                                                                  \33\[0m', nl].
prolog_message(user_versions) -->
    (   { findall(Msg, prolog:version_msg(Msg), Msgs),
          Msgs \== []
        }
    ->  [nl],
        user_version_messages(Msgs)
    ;   []
    ).
prolog_message(documentaton) -->
    [ 'For spiritual help, consult Kourosh or one of the tutors', nl,
      'For built-in help, use ?- kourosh_explain(Topic). or ?- help_me_kourosh(Word).'
    ].
prolog_message(welcome) -->
    [ 'Welcome to SWI-Rosh (' ],
    prolog_message(threads),
    prolog_message(address_bits),
    ['version ' ],
    prolog_message(version),
    [ ')', nl ],
    prolog_message(copyright),
    [ nl ],
    prolog_message(user_versions),
    [ nl ],
    prolog_message(documentaton),
    [ nl, nl ].
prolog_message(about) -->
    [ 'SWI-Rosh version (' ],
    prolog_message(threads),
    prolog_message(address_bits),
    ['version ' ],
    prolog_message(version),
    [ ')', nl ],
    prolog_message(copyright).
prolog_message(halt) -->
    [ 'Kourosh Out' ].
prolog_message(break(begin, Level)) -->
    [ 'Break level ~d'-[Level] ].
prolog_message(break(end, Level)) -->
    [ 'Exit break level ~d'-[Level] ].
prolog_message(var_query(_)) -->
    [ '... 1,000,000 ............ 10,000,000 years later', nl, nl,
      '~t~8|>> 42 << (last release gives the question)'
    ].
prolog_message(close_on_abort(Stream)) -->
    [ 'Abort: closed stream ~p'-[Stream] ].
prolog_message(cancel_halt(Reason)) -->
    [ 'Halt cancelled: ~p'-[Reason] ].
prolog_message(on_error(halt(Status))) -->
    { statistics(errors, Errors),
      statistics(warnings, Warnings)
    },
    [ 'Halting with status ~w due to ~D errors and ~D warnings'-
      [Status, Errors, Warnings] ].

prolog_message(query(QueryResult)) -->
    query_result(QueryResult).

query_result(no) -->            % failure
    [ ansi(truth(false), 'not_kourosh.', []) ],
    extra_line.
query_result(yes(true, [])) -->      % prompt_alternatives_on: groundness
    !,
    [ ansi(truth(true), 'kourosh.', []) ],
    extra_line.
query_result(yes(Delays, Residuals)) -->
    result([], Delays, Residuals),
    extra_line.
query_result(done) -->          % user typed <CR>
    extra_line.
query_result(yes(Bindings, Delays, Residuals)) -->
    result(Bindings, Delays, Residuals),
    prompt(yes, Bindings, Delays, Residuals).
query_result(more(Bindings, Delays, Residuals)) -->
    result(Bindings, Delays, Residuals),
    prompt(more, Bindings, Delays, Residuals).
query_result(help) -->
    [ nl, 'Kourosh Moves:'-[], nl, nl,
      '; (n, r, space, TAB): redo    t:          trace & redo'-[], nl,
      'b:                    break   c (a, RET): exit'-[], nl,
      'w:                    write   p           print'-[], nl,
      'h (?):                help'-[],
      nl, nl
    ].
query_result(action) -->
    [ 'Kourosh Moves? '-[], flush ].
query_result(confirm) -->
    [ 'Kourosh wants \'y\' or \'n\'? '-[], flush ].
query_result(eof) -->
    [ nl ].
query_result(toplevel_open_line) -->
    [].

prompt(Answer, [], true, []-[]) -->
    !,
    prompt(Answer, empty).
prompt(Answer, _, _, _) -->
    !,
    prompt(Answer, non_empty).

prompt(yes, empty) -->
    !,
    [ ansi(truth(true), 'kourosh.', []) ],
    extra_line.
prompt(yes, _) -->
    !,
    [ full_stop ],
    extra_line.
prompt(more, empty) -->
    !,
    [ ansi(truth(true), 'kourosh ', []), flush ].
prompt(more, _) -->
    !,
    [ ' '-[], flush ].

result(Bindings, Delays, Residuals) -->
    { current_prolog_flag(answer_write_options, Options0),
      Options = [partial(true)|Options0],
      GOptions = [priority(999)|Options0]
    },
    wfs_residual_program(Delays, GOptions),
    ["KOUROSH RECKONS:", nl],
    bindings(Bindings, [priority(699)|Options]),
    (   {Residuals == []-[]}
    ->  bind_delays_sep(Bindings, Delays),
        delays(Delays, GOptions)
    ;   bind_res_sep(Bindings, Residuals),
        residuals(Residuals, GOptions),
        (   {Delays == true}
        ->  []
        ;   [','-[], nl],
            delays(Delays, GOptions)
        )
    ).

bindings([], _) -->
    [].
bindings([binding(Names,Skel,Subst)|T], Options) -->
    { '$last'(Names, Name) },
    var_names(Names), value(Name, Skel, Subst, Options),
    (   { T \== [] }
    ->  [ ','-[], nl ],
        bindings(T, Options)
    ;   []
    ).

var_names([Name]) -->
    !,
    [ '~w = '-[Name] ].
var_names([Name1,Name2|T]) -->
    !,
    [ '~w = ~w, '-[Name1, Name2] ],
    var_names([Name2|T]).


value(Name, Skel, Subst, Options) -->
    (   { var(Skel), Subst = [Skel=S] }
    ->  { Skel = '$VAR'(Name) },
        [ '~W'-[S, Options] ]
    ;   [ '~W'-[Skel, Options] ],
        substitution(Subst, Options)
    ).

substitution([], _) --> !.
substitution([N=V|T], Options) -->
    [ ', ', ansi(comment, '% where', []), nl,
      '    ~w = ~W'-[N,V,Options] ],
    substitutions(T, Options).

substitutions([], _) --> [].
substitutions([N=V|T], Options) -->
    [ ','-[], nl, '    ~w = ~W'-[N,V,Options] ],
    substitutions(T, Options).


residuals(Normal-Hidden, Options) -->
    residuals1(Normal, Options),
    bind_res_sep(Normal, Hidden),
    (   {Hidden == []}
    ->  []
    ;   [ansi(comment, '% with pending residual goals', []), nl]
    ),
    residuals1(Hidden, Options).

residuals1([], _) -->
    [].
residuals1([G|Gs], Options) -->
    (   { Gs \== [] }
    ->  [ '~W,'-[G, Options], nl ],
        residuals1(Gs, Options)
    ;   [ '~W'-[G, Options] ]
    ).

wfs_residual_program(true, _Options) -->
    !.
wfs_residual_program(Goal, _Options) -->
    { current_prolog_flag(toplevel_list_wfs_residual_program, true),
      '$current_typein_module'(TypeIn),
      (   current_predicate(delays_residual_program/2)
      ->  true
      ;   use_module(library(wfs), [delays_residual_program/2])
      ),
      delays_residual_program(TypeIn:Goal, TypeIn:Program),
      Program \== []
    },
    !,
    [ ansi(comment, '% WFS residual program', []), nl ],
    [ ansi(wfs(residual_program), '~@', ['$messages':list_clauses(Program)]) ].
wfs_residual_program(_, _) --> [].

delays(true, _Options) -->
    !.
delays(Goal, Options) -->
    { current_prolog_flag(toplevel_list_wfs_residual_program, true)
    },
    !,
    [ ansi(truth(undefined), '~W', [Goal, Options]) ].
delays(_, _Options) -->
    [ ansi(truth(undefined), undefined, []) ].

:- public list_clauses/1.

list_clauses([]).
list_clauses([H|T]) :-
    (   system_undefined(H)
    ->  true
    ;   portray_clause(user_output, H, [indent(4)])
    ),
    list_clauses(T).

system_undefined((undefined :- tnot(undefined))).
system_undefined((answer_count_restraint :- tnot(answer_count_restraint))).
system_undefined((radial_restraint :- tnot(radial_restraint))).

bind_res_sep(_, []) --> !.
bind_res_sep(_, []-[]) --> !.
bind_res_sep([], _) --> !.
bind_res_sep(_, _) --> [','-[], nl].

bind_delays_sep([], _) --> !.
bind_delays_sep(_, true) --> !.
bind_delays_sep(_, _) --> [','-[], nl].

extra_line -->
    { current_prolog_flag(toplevel_extra_white_line, true) },
    !,
    ['~N'-[]].
extra_line -->
    [].

prolog_message(if_tty(Message)) -->
    (   {current_prolog_flag(tty_control, true)}
    ->  [ at_same_line | Message ]
    ;   []
    ).
prolog_message(halt(Reason)) -->
    [ '~w: Kourosh Out'-[Reason] ].
prolog_message(no_action(Char)) -->
    [ 'Unknown action: ~c (h for help)'-[Char], nl ].

prolog_message(history(help(Show, Help))) -->
    [ 'History Commands:', nl,
      '    !!.              Repeat last query', nl,
      '    !nr.             Repeat query numbered <nr>', nl,
      '    !str.            Repeat last query starting with <str>', nl,
      '    !?str.           Repeat last query holding <str>', nl,
      '    ^old^new.        Substitute <old> into <new> of last query', nl,
      '    !nr^old^new.     Substitute in query numbered <nr>', nl,
      '    !str^old^new.    Substitute in query starting with <str>', nl,
      '    !?str^old^new.   Substitute in query holding <str>', nl,
      '    ~w.~21|Show history list'-[Show], nl,
      '    ~w.~21|Show this list'-[Help], nl, nl
    ].
prolog_message(history(no_event)) -->
    [ '! No such event' ].
prolog_message(history(bad_substitution)) -->
    [ '! Bad substitution' ].
prolog_message(history(expanded(Event))) -->
    [ '~w.'-[Event] ].
prolog_message(history(history(Events))) -->
    history_events(Events).

history_events([]) -->
    [].
history_events([Nr/Event|T]) -->
    [ '~t~w   ~8|~W~W'-[ Nr,
                         Event, [partial(true)],
                         '.', [partial(true)]
                       ],
      nl
    ],
    history_events(T).


user_version_messages([]) --> [].
user_version_messages([H|T]) -->
    user_version_message(H),
    user_version_messages(T).

%!  user_version_message(+Term)

user_version_message(Term) -->
    translate_message2(Term), !, [nl].
user_version_message(Atom) -->
    [ '~w'-[Atom], nl ].


                 /*******************************
                 *       DEBUGGER MESSAGES      *
                 *******************************/

prolog_message(spy(Head)) -->
    { goal_to_predicate_indicator(Head, Pred)
    },
    [ 'Spy point on ~p'-[Pred] ].
prolog_message(nospy(Head)) -->
    { goal_to_predicate_indicator(Head, Pred)
    },
    [ 'Spy point removed from ~p'-[Pred] ].
prolog_message(trace_mode(OnOff)) -->
    [ 'Trace mode switched to ~w'-[OnOff] ].
prolog_message(debug_mode(OnOff)) -->
    [ 'Debug mode switched to ~w'-[OnOff] ].
prolog_message(debugging(OnOff)) -->
    [ 'Debug mode is ~w'-[OnOff] ].
prolog_message(spying([])) -->
    !,
    [ 'No spy points' ].
prolog_message(spying(Heads)) -->
    [ 'Spy points (see spy/1) on:', nl ],
    predicate_list(Heads).
prolog_message(trace(Head, [])) -->
    !,
    { goal_to_predicate_indicator(Head, Pred)
    },
    [ '        ~p: Not tracing'-[Pred], nl].
prolog_message(trace(Head, Ports)) -->
    { goal_to_predicate_indicator(Head, Pred)
    },
    [ '        ~p: ~w'-[Pred, Ports], nl].
prolog_message(tracing([])) -->
    !,
    [ 'No traced predicates (see trace/1)' ].
prolog_message(tracing(Heads)) -->
    [ 'Trace points (see trace/1) on:', nl ],
    tracing_list(Heads).

predicate_list([]) -->                  % TBD: Share with dwim, etc.
    [].
predicate_list([H|T]) -->
    { goal_to_predicate_indicator(H, Pred)
    },
    [ '        ~p'-[Pred], nl],
    predicate_list(T).

tracing_list([]) -->
    [].
tracing_list([trace(Head, Ports)|T]) -->
    translate_message(trace(Head, Ports)),
    tracing_list(T).

prolog_message(frame(Frame, backtrace, _PC)) -->
    !,
    { prolog_frame_attribute(Frame, level, Level)
    },
    [ ansi(frame(level), '~t[~D] ~10|', [Level]) ],
    frame_context(Frame),
    frame_goal(Frame).
prolog_message(frame(Frame, choice, PC)) -->
    !,
    prolog_message(frame(Frame, backtrace, PC)).
prolog_message(frame(_, cut_call, _)) --> !, [].
prolog_message(frame(Goal, trace(Port))) -->
    !,
    thread_context,
    [ ' T ' ],
    port(Port),
    goal(Goal).
prolog_message(frame(Goal, trace(Port, Id))) -->
    !,
    thread_context,
    [ ' T ' ],
    port(Port, Id),
    goal(Goal).
prolog_message(frame(Frame, Port, _PC)) -->
    frame_flags(Frame),
    port(Port),
    frame_level(Frame),
    frame_context(Frame),
    frame_depth_limit(Port, Frame),
    frame_goal(Frame),
    [ flush ].

frame_goal(Frame) -->
    { prolog_frame_attribute(Frame, goal, Goal)
    },
    goal(Goal).

goal(Goal0) -->
    { clean_goal(Goal0, Goal),
      current_prolog_flag(debugger_write_options, Options)
    },
    [ '~W'-[Goal, Options] ].

frame_level(Frame) -->
    { prolog_frame_attribute(Frame, level, Level)
    },
    [ '(~D) '-[Level] ].

frame_context(Frame) -->
    (   { current_prolog_flag(debugger_show_context, true),
          prolog_frame_attribute(Frame, context_module, Context)
        }
    ->  [ '[~w] '-[Context] ]
    ;   []
    ).

frame_depth_limit(fail, Frame) -->
    { prolog_frame_attribute(Frame, depth_limit_exceeded, true)
    },
    !,
    [ '[depth-limit exceeded] ' ].
frame_depth_limit(_, _) -->
    [].

frame_flags(Frame) -->
    { prolog_frame_attribute(Frame, goal, Goal),
      (   predicate_property(Goal, transparent)
      ->  T = '^'
      ;   T = ' '
      ),
      (   predicate_property(Goal, spying)
      ->  S = '*'
      ;   S = ' '
      )
    },
    [ '~w~w '-[T, S] ].

% trace/1,2 context handling
port(Port, _Id-Level) -->
    [ '[~d] '-Level ],
    port(Port).

port(Port) -->
    { port_name(Port, Name)
    },
    !,
    [ ansi(port(Port), '~w: ', [Name]) ].

port_name(call,      'Call').
port_name(exit,      'Exit').
port_name(fail,      'Fail').
port_name(redo,      'Redo').
port_name(unify,     'Unify').
port_name(exception, 'Exception').

clean_goal(M:Goal, Goal) :-
    hidden_module(M),
    !.
clean_goal(M:Goal, Goal) :-
    predicate_property(M:Goal, built_in),
    !.
clean_goal(Goal, Goal).


                 /*******************************
                 *        COMPATIBILITY         *
                 *******************************/

prolog_message(compatibility(renamed(Old, New))) -->
    [ 'The predicate ~p has been renamed to ~p.'-[Old, New], nl,
      'Please update your sources for compatibility with future versions.'
    ].


                 /*******************************
                 *            THREADS           *
                 *******************************/

prolog_message(abnormal_thread_completion(Goal, exception(Ex))) -->
    !,
    [ 'Thread running "~p" died on exception: '-[Goal] ],
    translate_message(Ex).
prolog_message(abnormal_thread_completion(Goal, fail)) -->
    [ 'Thread running "~p" died due to failure'-[Goal] ].
prolog_message(threads_not_died(Running)) -->
    [ 'The following threads wouldn\'t die: ~p'-[Running] ].


                 /*******************************
                 *             PACKS            *
                 *******************************/

prolog_message(pack(attached(Pack, BaseDir))) -->
    [ 'Attached package ~w at ~q'-[Pack, BaseDir] ].
prolog_message(pack(duplicate(Entry, OldDir, Dir))) -->
    [ 'Package ~w already attached at ~q.'-[Entry,OldDir], nl,
      '\tIgnoring version from ~q'- [Dir]
    ].
prolog_message(pack(no_arch(Entry, Arch))) -->
    [ 'Package ~w: no binary for architecture ~w'-[Entry, Arch] ].

                 /*******************************
                 *             MISC             *
                 *******************************/

prolog_message(null_byte_in_path(Component)) -->
    [ '0-byte in PATH component: ~p (skipped directory)'-[Component] ].
prolog_message(invalid_tmp_dir(Dir, Reason)) -->
    [ 'Cannot use ~p as temporary file directory: ~w'-[Dir, Reason] ].
prolog_message(ambiguous_stream_pair(Pair)) -->
    [ 'Ambiguous operation on stream pair ~p'-[Pair] ].
prolog_message(backcomp(init_file_moved(FoundFile))) -->
    { absolute_file_name(app_config('init.pl'), InitFile,
                         [ file_errors(fail)
                         ])
    },
    [ 'The location of the config file has moved'-[], nl,
      '  from "~w"'-[FoundFile], nl,
      '  to   "~w"'-[InitFile], nl,
      '  See https://www.SWI-Rosh.org/modified/config-files.html'-[]
    ].

		 /*******************************
		 *          DEPRECATED		*
		 *******************************/

deprecated(Term) -->
    prolog:deprecated(Term),
    !.
deprecated(set_prolog_stack(_Stack,limit)) -->
    [ 'set_prolog_stack/2: limit(Size) sets the combined limit.'-[], nl,
      'See https://www.SWI-Rosh.org/changes/stack-limit.html'
    ].

		 /*******************************
		 *           TRIPWIRES		*
		 *******************************/

tripwire_message(Wire, Context) -->
    [ 'Trapped tripwire ~w for '-[Wire] ],
    tripwire_context(Wire, Context).

tripwire_context(_, ATrie) -->
    { '$is_answer_trie'(ATrie, _),
      !,
      '$tabling':atrie_goal(ATrie, QGoal),
      user_predicate_indicator(QGoal, Goal)
    },
    [ '~p'-[Goal] ].
tripwire_context(_, Ctx) -->
    [ '~p'-[Ctx] ].


		 /*******************************
		 *        DEFAULT THEME		*
		 *******************************/

:- public default_theme/2.

default_theme(var,                    [fg(red)]).
default_theme(code,                   [fg(blue)]).
default_theme(comment,                [fg(green)]).
default_theme(warning,                [fg(red)]).
default_theme(error,                  [bold, fg(red)]).
default_theme(truth(false),           [bold, fg(red)]).
default_theme(truth(true),            [bold]).
default_theme(truth(undefined),       [bold, fg(cyan)]).
default_theme(wfs(residual_program),  [fg(cyan)]).
default_theme(frame(level),           [bold]).
default_theme(port(call),             [bold, fg(green)]).
default_theme(port(exit),             [bold, fg(green)]).
default_theme(port(fail),             [bold, fg(red)]).
default_theme(port(redo),             [bold, fg(yellow)]).
default_theme(port(unify),            [bold, fg(blue)]).
default_theme(port(exception),        [bold, fg(magenta)]).
default_theme(message(informational), [fg(green)]).
default_theme(message(information),   [fg(green)]).
default_theme(message(debug(_)),      [fg(blue)]).
default_theme(message(Level),         Attrs) :-
    nonvar(Level),
    default_theme(Level, Attrs).


                 /*******************************
                 *      PRINTING MESSAGES       *
                 *******************************/

:- multifile
    user:message_hook/3,
    prolog:message_prefix_hook/2.
:- dynamic
    user:message_hook/3,
    prolog:message_prefix_hook/2.
:- thread_local
    user:thread_message_hook/3.
:- '$hide'((push_msg/1,pop_msg/0)).

%!  print_message(+Kind, +Term)
%
%   Print an error message using a term as generated by the exception
%   system.

print_message(Level, Term) :-
    setup_call_cleanup(
        push_msg(Term),
        print_message_guarded(Level, Term),
        pop_msg),
    !.
print_message(Level, Term) :-
    (   Level \== silent
    ->  format(user_error, 'Recursive ~w message: ~q~n', [Level, Term])
    ;   true
    ).

push_msg(Term) :-
    nb_current('$inprint_message', Messages),
    !,
    \+ ( '$member'(Msg, Messages),
         Msg =@= Term
       ),
    b_setval('$inprint_message', [Term|Messages]).
push_msg(Term) :-
    b_setval('$inprint_message', [Term]).

pop_msg :-
    (   nb_current('$inprint_message', [_|Messages]),
        Messages \== []
    ->  b_setval('$inprint_message', Messages)
    ;   nb_delete('$inprint_message'),              % delete history
        b_setval('$inprint_message', [])
    ).

print_message_guarded(Level, Term) :-
    (   must_print(Level, Term)
    ->  (   translate_message(Term, Lines, [])
        ->  (   nonvar(Term),
                (   notrace(user:thread_message_hook(Term, Level, Lines))
                ->  true
                ;   notrace(user:message_hook(Term, Level, Lines))
                )
            ->  true
            ;   '$inc_message_count'(Level),
                print_system_message(Term, Level, Lines),
                maybe_halt_on_error(Level)
            )
        )
    ;   true
    ).

maybe_halt_on_error(error) :-
    current_prolog_flag(on_error, halt),
    !,
    halt(1).
maybe_halt_on_error(warning) :-
    current_prolog_flag(on_warning, halt),
    !,
    halt(1).
maybe_halt_on_error(_).


%!  print_system_message(+Term, +Kind, +Lines)
%
%   Print the message if the user did not intecept the message.
%   The first is used for errors and warnings that can be related
%   to source-location.  Note that syntax errors have their own
%   source-location and should therefore not be handled this way.

print_system_message(_, silent, _) :- !.
print_system_message(_, informational, _) :-
    current_prolog_flag(verbose, silent),
    !.
print_system_message(_, banner, _) :-
    current_prolog_flag(verbose, silent),
    !.
print_system_message(_, _, []) :- !.
print_system_message(Term, Kind, Lines) :-
    catch(flush_output(user_output), _, true),      % may not exist
    source_location(File, Line),
    Term \= error(syntax_error(_), _),
    msg_property(Kind, location_prefix(File:Line, LocPrefix, LinePrefix)),
    !,
    insert_prefix(Lines, LinePrefix, Ctx, PrefixLines),
    '$append'([ begin(Kind, Ctx),
                LocPrefix,
                nl
              | PrefixLines
              ],
              [ end(Ctx)
              ],
              AllLines),
    msg_property(Kind, stream(Stream)),
    ignore(stream_property(Stream, position(Pos))),
    print_message_lines(Stream, AllLines),
    (   \+ stream_property(Stream, position(Pos)),
        msg_property(Kind, wait(Wait)),
        Wait > 0
    ->  sleep(Wait)
    ;   true
    ).
print_system_message(_, Kind, Lines) :-
    msg_property(Kind, stream(Stream)),
    print_message_lines(Stream, kind(Kind), Lines).

:- multifile
    user:message_property/2.

msg_property(Kind, Property) :-
    notrace(user:message_property(Kind, Property)),
    !.
msg_property(Kind, prefix(Prefix)) :-
    msg_prefix(Kind, Prefix),
    !.
msg_property(_, prefix('~N')) :- !.
msg_property(query, stream(user_output)) :- !.
msg_property(_, stream(user_error)) :- !.
msg_property(error,
             location_prefix(File:Line,
                             '~NDISSAPOINTED KOUROSH: ~w:~d:'-[File,Line],
                             '~NDISSAPOINTED KOUROSH:    ')) :- !.
msg_property(warning,
             location_prefix(File:Line,
                             '~NWarning: ~w:~d:'-[File,Line],
                             '~NWarning:    ')) :- !.
msg_property(error,   wait(0.1)) :- !.

msg_prefix(debug(_), Prefix) :-
    msg_context('~N% ', Prefix).
msg_prefix(warning, Prefix) :-
    msg_context('~NWarning: ', Prefix).
msg_prefix(error, Prefix) :-
    msg_context('~NDISSAPOINTED KOUROSH: ', Prefix).
msg_prefix(informational, '~N% ').
msg_prefix(information,   '~N% ').

%!  msg_context(+Prefix0, -Prefix) is det.
%
%   Add contextual information to a message.   This uses the Prolog flag
%   `message_context`. Recognised context terms are:
%
%     - time
%     - time(Format)
%     - thread
%
%   In addition, the hook prolog:message_prefix_hook/2   is  called that
%   allows for additional context information.

msg_context(Prefix0, Prefix) :-
    current_prolog_flag(message_context, Context),
    is_list(Context),
    !,
    add_message_context(Context, Prefix0, Prefix).
msg_context(Prefix, Prefix).

add_message_context([], Prefix, Prefix).
add_message_context([H|T], Prefix0, Prefix) :-
    (   add_message_context1(H, Prefix0, Prefix1)
    ->  true
    ;   Prefix1 = Prefix0
    ),
    add_message_context(T, Prefix1, Prefix).

add_message_context1(Context, Prefix0, Prefix) :-
    prolog:message_prefix_hook(Context, Extra),
    atomics_to_string([Prefix0, Extra, ' '], Prefix).
add_message_context1(time, Prefix0, Prefix) :-
    get_time(Now),
    format_time(string(S), '%T.%3f ', Now),
    string_concat(Prefix0, S, Prefix).
add_message_context1(time(Format), Prefix0, Prefix) :-
    get_time(Now),
    format_time(string(S), Format, Now),
    atomics_to_string([Prefix0, S, ' '], Prefix).
add_message_context1(thread, Prefix0, Prefix) :-
    thread_self(Id0),
    Id0 \== main,
    !,
    (   atom(Id0)
    ->  Id = Id0
    ;   thread_property(Id0, id(Id))
    ),
    format(string(Prefix), '~w[Thread ~w] ', [Prefix0, Id]).

%!  print_message_lines(+Stream, +PrefixOrKind, +Lines)
%
%   Quintus compatibility predicate to print message lines using
%   a prefix.

print_message_lines(Stream, kind(Kind), Lines) :-
    !,
    msg_property(Kind, prefix(Prefix)),
    insert_prefix(Lines, Prefix, Ctx, PrefixLines),
    '$append'([ begin(Kind, Ctx)
              | PrefixLines
              ],
              [ end(Ctx)
              ],
              AllLines),
    print_message_lines(Stream, AllLines).
print_message_lines(Stream, Prefix, Lines) :-
    insert_prefix(Lines, Prefix, _, PrefixLines),
    print_message_lines(Stream, PrefixLines).

%!  insert_prefix(+Lines, +Prefix, +Ctx, -PrefixedLines)

insert_prefix([at_same_line|Lines0], Prefix, Ctx, Lines) :-
    !,
    prefix_nl(Lines0, Prefix, Ctx, Lines).
insert_prefix(Lines0, Prefix, Ctx, [prefix(Prefix)|Lines]) :-
    prefix_nl(Lines0, Prefix, Ctx, Lines).

prefix_nl([], _, _, [nl]).
prefix_nl([nl], _, _, [nl]) :- !.
prefix_nl([flush], _, _, [flush]) :- !.
prefix_nl([nl|T0], Prefix, Ctx, [nl, prefix(Prefix)|T]) :-
    !,
    prefix_nl(T0, Prefix, Ctx, T).
prefix_nl([ansi(Attrs,Fmt,Args)|T0], Prefix, Ctx,
          [ansi(Attrs,Fmt,Args,Ctx)|T]) :-
    !,
    prefix_nl(T0, Prefix, Ctx, T).
prefix_nl([H|T0], Prefix, Ctx, [H|T]) :-
    prefix_nl(T0, Prefix, Ctx, T).

%!  print_message_lines(+Stream, +Lines)

print_message_lines(Stream, Lines) :-
    with_output_to(
        Stream,
        notrace(print_message_lines_guarded(current_output, Lines))).

print_message_lines_guarded(_, []) :- !.
print_message_lines_guarded(S, [H|T]) :-
    line_element(S, H),
    print_message_lines_guarded(S, T).

line_element(S, E) :-
    prolog:message_line_element(S, E),
    !.
line_element(S, full_stop) :-
    !,
    '$put_token'(S, '.').           % insert space if needed.
line_element(S, nl) :-
    !,
    nl(S).
line_element(S, prefix(Fmt-Args)) :-
    !,
    safe_format(S, Fmt, Args).
line_element(S, prefix(Fmt)) :-
    !,
    safe_format(S, Fmt, []).
line_element(S, flush) :-
    !,
    flush_output(S).
line_element(S, Fmt-Args) :-
    !,
    safe_format(S, Fmt, Args).
line_element(S, ansi(_, Fmt, Args)) :-
    !,
    safe_format(S, Fmt, Args).
line_element(S, ansi(_, Fmt, Args, _Ctx)) :-
    !,
    safe_format(S, Fmt, Args).
line_element(_, begin(_Level, _Ctx)) :- !.
line_element(_, end(_Ctx)) :- !.
line_element(S, Fmt) :-
    safe_format(S, Fmt, []).

%!  safe_format(+Stream, +Format, +Args) is det.

safe_format(S, Fmt, Args) :-
    E = error(_,_),
    catch(format(S,Fmt,Args), E,
          format_failed(S,Fmt,Args,E)).

format_failed(S, _Fmt, _Args, E) :-
    E = error(io_error(_,S),_),
    !,
    throw(E).
format_failed(S, Fmt, Args, error(E,_)) :-
    format(S, '~N    [[ EXCEPTION while printing message ~q~n\c
                        ~7|with arguments ~W:~n\c
                        ~7|raised: ~W~n~4|]]~n',
           [ Fmt,
             Args, [quoted(true), max_depth(10)],
             E, [quoted(true), max_depth(10)]
           ]).

%!  message_to_string(+Term, -String)
%
%   Translate an error term into a string

message_to_string(Term, Str) :-
    translate_message(Term, Actions, []),
    !,
    actions_to_format(Actions, Fmt, Args),
    format(string(Str), Fmt, Args).

actions_to_format([], '', []) :- !.
actions_to_format([nl], '', []) :- !.
actions_to_format([Term, nl], Fmt, Args) :-
    !,
    actions_to_format([Term], Fmt, Args).
actions_to_format([nl|T], Fmt, Args) :-
    !,
    actions_to_format(T, Fmt0, Args),
    atom_concat('~n', Fmt0, Fmt).
actions_to_format([ansi(_Attrs, Fmt0, Args0)|Tail], Fmt, Args) :-
    !,
    actions_to_format(Tail, Fmt1, Args1),
    atom_concat(Fmt0, Fmt1, Fmt),
    append_args(Args0, Args1, Args).
actions_to_format([Fmt0-Args0|Tail], Fmt, Args) :-
    !,
    actions_to_format(Tail, Fmt1, Args1),
    atom_concat(Fmt0, Fmt1, Fmt),
    append_args(Args0, Args1, Args).
actions_to_format([Skip|T], Fmt, Args) :-
    action_skip(Skip),
    !,
    actions_to_format(T, Fmt, Args).
actions_to_format([Term|Tail], Fmt, Args) :-
    atomic(Term),
    !,
    actions_to_format(Tail, Fmt1, Args),
    atom_concat(Term, Fmt1, Fmt).
actions_to_format([Term|Tail], Fmt, Args) :-
    actions_to_format(Tail, Fmt1, Args1),
    atom_concat('~w', Fmt1, Fmt),
    append_args([Term], Args1, Args).

action_skip(at_same_line).
action_skip(flush).
action_skip(begin(_Level, _Ctx)).
action_skip(end(_Ctx)).

append_args(M:Args0, Args1, M:Args) :-
    !,
    strip_module(Args1, _, A1),
    '$append'(Args0, A1, Args).
append_args(Args0, Args1, Args) :-
    strip_module(Args1, _, A1),
    '$append'(Args0, A1, Args).


                 /*******************************
                 *    MESSAGES TO PRINT ONCE    *
                 *******************************/

:- dynamic
    printed/2.

%!  print_once(Message, Level)
%
%   True for messages that must be printed only once.

print_once(compatibility(_), _).
print_once(null_byte_in_path(_), _).
print_once(deprecated(_), _).

%!  must_print(+Level, +Message)
%
%   True if the message must be printed.

must_print(Level, Message) :-
    nonvar(Message),
    print_once(Message, Level),
    !,
    \+ printed(Message, Level),
    assert(printed(Message, Level)).
must_print(_, _).

