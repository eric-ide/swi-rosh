/*  $Id$

    Part of SWI-Prolog

    Author:        Jan Wielemaker
    E-mail:        J.Wielemaker@uva.nl
    WWW:           http://www.swi-prolog.org
    Copyright (C): 1985-2008, University of Amsterdam

    This program is free software; you can redistribute it and/or
    modify it under the terms of the GNU General Public License
    as published by the Free Software Foundation; either version 2
    of the License, or (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU Lesser General Public
    License along with this library; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

    As a special exception, if you link this library with other files,
    compiled with a Free Software compiler, to produce an executable, this
    library does not by itself cause the resulting executable to be covered
    by the GNU General Public License. This exception does not however
    invalidate any other reasons why the executable file might be covered by
    the GNU General Public License.
*/

:- module(http_header,
	  [ http_read_request/2,	% +Stream, -Request
	    http_read_reply_header/2,	% +Stream, -Reply
	    http_reply/2,		% +What, +Stream
	    http_reply/3,		% +What, +Stream, +HdrExtra
	    http_reply_header/3,	% +Stream, +What, +HdrExtra

	    http_timestamp/2,		% +Time, -HTTP string

	    http_post_data/3,		% +Stream, +Data, +HdrExtra

	    http_read_header/2,		% +Fd, -Header
	    http_parse_header/2,	% +Codes, -Header
	    http_join_headers/3,	% +Default, +InHdr, -OutHdr
	    http_update_encoding/3,	% +HeaderIn, -Encoding, -HeaderOut
	    http_update_connection/4,	% +HeaderIn, +Request, -Connection, -HeaderOut
	    http_update_transfer/4	% +HeaderIn, +Request, -Transfer, -HeaderOut
	  ]).
:- use_module(library(readutil)).
:- use_module(library(debug)).
:- use_module(library(lists)).
:- use_module(library(url)).
:- use_module(library(memfile)).
:- use_module(library(settings)).
:- use_module(library(error)).
:- use_module(dcg_basics).
:- use_module(html_write).
:- use_module(mimetype).
:- use_module(mimepack).


% see http_update_transfer/4.

:- setting(http:chunked_transfer, oneof([never,on_request,if_possible]),
	   on_request, 'When to use Transfer-Encoding: Chunked').


		 /*******************************
		 *	    READ REQUEST	*
		 *******************************/

%%	http_read_request(+FdIn:stream, -Request) is det.
%
%	Read an HTTP request-header from FdIn and return the broken-down
%	request fields as +Name(+Value) pairs  in   a  list.  Request is
%	unified to =end_of_file= if FdIn is at the end of input.

http_read_request(In, Request) :-
	read_line_to_codes(In, Codes),
	(   Codes == end_of_file
	->  debug(http(header), 'end-of-file', []),
	    Request = end_of_file
	;   debug(http(header), 'First line: ~s~n', [Codes]),
	    Request =  [input(In)|Request1],
	    phrase(request(In, Request1), Codes),
	    (	Request1 = [unknown(Text)|_]
	    ->	string_to_list(S, Text),
		domain_error(http_request, S)
	    ;	true
	    )
	).


%%	http_read_reply_header(+FdIn, -Reply)
%
%	Read the HTTP reply header. Throws   an exception if the current
%	input does not contain a valid reply header.

http_read_reply_header(In, [input(In)|Reply]) :-
	read_line_to_codes(In, Codes),
	(   Codes == end_of_file
	->  debug(http(header), 'end-of-file', []),
	    throw(error(syntax(http_reply_header, end_of_file), _))
	;   debug(http(header), 'First line: ~s~n', [Codes]),
	    (   phrase(reply(In, Reply), Codes)
	    ->  true
	    ;   throw(error(syntax(http_reply_header, Codes), _))
	    )
	).


		 /*******************************
		 *	  FORMULATE REPLY	*
		 *******************************/

%%	http_reply(+Data, +Out:stream) is det.
%%	http_reply(+Data, +Out:stream, +HdrExtra) is det.
%
%	Data is one of
%	
%		* html(HTML)
%		HTML tokens as produced by html//1 from html_write.pl
%		
%		* file(+MimeType, +FileName)
%		Reply content of FileName using MimeType
%		
%		* tmp_file(+MimeType, +FileName)
%		Same as =file=, but do not include modification time
%		
%		* stream(+In, +Len)
%		Reply content of stream.
%		
%		* cgi_stream(+In, +Len)
%		Reply content of stream, which should start with an
%		HTTP header, followed by a blank line.  This is the
%		typical output from a CGI script.
%		
%	@tbd	Complete documentation	

http_reply(What, Out) :-
	http_reply(What, Out, [connection(close)]).

http_reply(html(HTML), Out, HrdExtra) :- !,
	phrase(reply_header(html(HTML), HrdExtra), Header),
	format(Out, '~s', [Header]),
	print_html(Out, HTML).
http_reply(file(Type, File), Out, HrdExtra) :- !,
	phrase(reply_header(file(Type, File), HrdExtra), Header),
	format(Out, '~s', [Header]),
	open(File, read, In, [type(binary)]),
	call_cleanup(copy_stream_data(In, Out),
		     close(In)).
http_reply(tmp_file(Type, File), Out, HrdExtra) :- !,
	phrase(reply_header(tmp_file(Type, File), HrdExtra), Header),
	format(Out, '~s', [Header]),
	open(File, read, In, [type(binary)]),
	call_cleanup(copy_stream_data(In, Out),
		     close(In)).
http_reply(stream(In, Len), Out, HdrExtra) :- !,
	phrase(reply_header(cgi_data(Len), HdrExtra), Header),
	format(Out, '~s', [Header]),
	copy_stream_data(In, Out).
http_reply(cgi_stream(In, Len), Out, HrdExtra) :- !,
	http_read_header(In, CgiHeader),
	seek(In, 0, current, Pos),
	Size is Len - Pos,
	http_join_headers(HrdExtra, CgiHeader, Hdr2),
	phrase(reply_header(cgi_data(Size), Hdr2), Header),
	format(Out, '~s', [Header]),
	copy_stream_data(In, Out).
http_reply(Status, Out, HdrExtra) :-
	set_stream(Out, encoding(utf8)),
	call_cleanup(http_status_reply(Status, Out, HdrExtra),
		     set_stream(Out, encoding(octet))), !.

%%	http_status_reply(+Status, +Out, +HdrExtra) is det.
%
%	Emit HTML non-200 status reports.

http_status_reply(moved(To), Out, HrdExtra) :- !,
	phrase(page([ title('301 Moved Permanently')
		    ],
		    [ h1('Moved Permanently'),
		      p(['The document has moved ',
			 a(href(To), ' Here')
			]),
		      \address
		    ]),
	       HTML),
	phrase(reply_header(moved(To, HTML), HrdExtra), Header),
	format(Out, '~s', [Header]),
	print_html(Out, HTML).
http_status_reply(moved_temporary(To), Out, HrdExtra) :- !,
	phrase(page([ title('302 Moved Temporary')
		    ],
		    [ h1('Moved Temporary'),
		      p(['The document is currently ',
			 a(href(To), ' Here')
			]),
		      \address
		    ]),
	       HTML),
	phrase(reply_header(moved_temporary(To, HTML), HrdExtra), Header),
	format(Out, '~s', [Header]),
	print_html(Out, HTML).
http_status_reply(see_other(To),Out,HdrExtra) :- !,
       phrase(page([ title('303 See Other')
                    ],
                    [ h1('See Other'),
                      p(['See other document ',
                         a(href(To), ' Here')
                        ]),
                      \address
                    ]),
               HTML),
        phrase(reply_header(see_other(To, HTML), HdrExtra), Header),
        format(Out, '~s', [Header]),
        print_html(Out, HTML).
http_status_reply(not_found(URL), Out, HrdExtra) :- !,
	phrase(page([ title('404 Not Found')
		    ],
		    [ h1('Not Found'),
		      p(['The requested URL ', tt(URL),
			 ' was not found on this server'
			]),
		      \address
		    ]),
	       HTML),
	phrase(reply_header(status(not_found, HTML), HrdExtra), Header),
	format(Out, '~s', [Header]),
	print_html(Out, HTML).
http_status_reply(forbidden(URL), Out, HrdExtra) :- !,
	phrase(page([ title('403 Forbidden')
		    ],
		    [ h1('Forbidden'),
		      p(['You don\'t have permission to access ', URL,
			 ' on this server'
			]),
		      \address
		    ]),
	       HTML),
	phrase(reply_header(status(forbidden, HTML), HrdExtra), Header),
	format(Out, '~s', [Header]),
	print_html(Out, HTML).
http_status_reply(authorise(Method, Realm), Out, HrdExtra) :- !,
	phrase(page([ title('401 Authorization Required')
		    ],
		    [ h1('Authorization Required'),
		      p(['This server could not verify that you ',
			 'are authorized to access the document ',
			 'requested.  Either you supplied the wrong ',
			 'credentials (e.g., bad password), or your ',
			 'browser doesn\'t understand how to supply ',
			 'the credentials required.'
			]),
		      \address
		    ]),
	       HTML),
	phrase(reply_header(authorise(Method, Realm, HTML), HrdExtra), Header),
	format(Out, '~s', [Header]),
	print_html(Out, HTML).
http_status_reply(not_modified, Out, HrdExtra) :- !,
	phrase(reply_header(status(not_modified), HrdExtra), Header),
	format(Out, '~s', [Header]).
http_status_reply(server_error(ErrorTerm), Out, HrdExtra) :-
	'$messages':translate_message(ErrorTerm, Lines, []),
	phrase(page([ title('500 Internal server error')
		    ],
		    [ h1('Internal server error'),
		      p(\html_message_lines(Lines)),
		      \address
		    ]),
	       HTML),
	phrase(reply_header(status(server_error, HTML), HrdExtra), Header),
	format(Out, '~s', [Header]),
	print_html(Out, HTML).
http_status_reply(unavailable(WhyHTML), Out, HdrExtra) :- !,
	phrase(page([ title('503 Service Unavailable')
		    ],
		    [ h1('Service Unavailable'),
		      WhyHTML,
		      \address
		    ]),
	       HTML),
	phrase(reply_header(status(service_unavailable, HTML), HdrExtra), Header),
	format(Out, '~s', [Header]),
	print_html(Out, HTML).
http_status_reply(resource_error(ErrorTerm), Out, HdrExtra) :- !,
	'$messages':translate_message(ErrorTerm, Lines, []),
	http_status_reply(unavailable(p(\html_message_lines(Lines))), Out, HdrExtra).
http_status_reply(busy, Out, HdrExtra) :- !,
	HTML = p(['The server is temporarily out of resources, please try again later']),
	http_status_reply(unavailable(HTML), Out, HdrExtra).


html_message_lines([]) -->
	[].
html_message_lines([nl|T]) --> !,
	html([br([])]),
	html_message_lines(T).
html_message_lines([flush]) -->
	[].
html_message_lines([Fmt-Args|T]) --> !,
	{ format(string(S), Fmt, Args)
	},
	html([S]),
	html_message_lines(T).
html_message_lines([Fmt|T]) --> !,
	{ format(string(S), Fmt, [])
	},
	html([S]),
	html_message_lines(T).

%%	http_join_headers(+Default, +Header, -Out)
%	
%	Append headers from Default to Header if they are not
%	already part of it.

http_join_headers([], H, H).
http_join_headers([H|T], Hdr0, Hdr) :-
	functor(H, N, A),
	functor(H2, N, A),
	member(H2, Hdr0), !,
	http_join_headers(T, Hdr0, Hdr).
http_join_headers([H|T], Hdr0, [H|Hdr]) :-
	http_join_headers(T, Hdr0, Hdr).


%%	http_update_encoding(+HeaderIn, -Encoding, -HeaderOut)
%	
%	Allow for rewrite of the  header,   adjusting  the  encoding. We
%	distinguish three options. If  the   user  announces  `text', we
%	always use UTF-8 encoding. If   the user announces charset=utf-8
%	we  use  UTF-8  and  otherwise  we  use  octet  (raw)  encoding.
%	Alternatively we could dynamically choose for ASCII, ISO-Latin-1
%	or UTF-8.

http_update_encoding(Header0, utf8, [content_type(Type)|Header]) :-
	select(content_type(Type0), Header0, Header),
	sub_atom(Type0, 0, _, _, 'text/'), !,
	(   sub_atom(Type0, S, _, _, ';')
	->  sub_atom(Type0, 0, S, _, B)
	;   B = Type0
	),
	atom_concat(B, '; charset=UTF-8', Type).
http_update_encoding(Header, Encoding, Header) :-
	memberchk(content_type(Type), Header),
	(   (   sub_atom(Type, _, _, _, 'UTF-8')
	    ;   sub_atom(Type, _, _, _, 'utf-8')
	    )
	->  Encoding = utf8
	;   mime_type_encoding(Type, Encoding)
	).
http_update_encoding(Header, octet, Header).

%%	mime_type_encoding(+MimeType, -Encoding) is semidet.
%
%	Encoding is the (default) character encoding for MimeType.

mime_type_encoding('application/json', utf8).
mime_type_encoding('application/jsonrequest', utf8).


%%	http_update_connection(+CGIHeader, +Request, -Connection, -Header)
%
%	Merge keep-alive information from  Request   and  CGIHeader into
%	Header.

http_update_connection(CgiHeader, Request, Connect, [connection(Connect)|Rest]) :-
	select(connection(CgiConn), CgiHeader, Rest), !,
	connection(Request, ReqConnection),
	join_connection(ReqConnection, CgiConn, Connect).
http_update_connection(CgiHeader, Request, Connect, [connection(Connect)|CgiHeader]) :-
	connection(Request, Connect).

join_connection(Keep1, Keep2, Connection) :-
	(   downcase_atom(Keep1, 'keep-alive'),
	    downcase_atom(Keep2, 'keep-alive')
	->  Connection = 'Keep-Alive'
	;   Connection = close
	).


%%	connection(+Header, -Connection)
%	
%	Extract the desired connection from a header.

connection(Header, Close) :-
	(   memberchk(connection(Connection), Header)
	->  Close = Connection
	;   memberchk(http_version(1-X), Header),
	    X >= 1
	->  Close = 'Keep-Alive'
	;   Close = close
	).


%%	http_update_transfer(+Request, +CGIHeader, -Transfer, -Header)
%
%	Decide on the transfer encoding  from   the  Request and the CGI
%	header.    The    behaviour    depends      on    the    setting
%	http:chunked_transfer. If =never=, even   explitic  requests are
%	ignored. If =on_request=, chunked encoding  is used if requested
%	through  the  CGI  header  and  allowed    by   the  client.  If
%	=if_possible=, chunked encoding is  used   whenever  the  client
%	allows for it, which is  interpreted   as  the client supporting
%	HTTP 1.1 or higher.
%	
%	Chunked encoding is more space efficient   and allows the client
%	to start processing partial results. The drawback is that errors
%	lead to incomplete pages instead of  a nicely formatted complete
%	page.

http_update_transfer(Request, CgiHeader, Transfer, Header) :-
	setting(http:chunked_transfer, When),
	http_update_transfer(When, Request, CgiHeader, Transfer, Header).

http_update_transfer(never, _, CgiHeader, none, Header) :- !,
	delete(CgiHeader, transfer_encoding(_), Header).
http_update_transfer(_, Request, CgiHeader, Transfer, Header) :-
	select(transfer_encoding(CgiTransfer), CgiHeader, Rest), !,
	transfer(Request, ReqConnection),
	join_transfer(ReqConnection, CgiTransfer, Transfer),
	(   Transfer == none
	->  Header = Rest
	;   Header = [transfer_encoding(Transfer)|Rest]
	).
http_update_transfer(if_possible, Request, CgiHeader, Transfer, Header) :-
	transfer(Request, Transfer),
	Transfer \== none, !,
	Header = [transfer_encoding(Transfer)|CgiHeader].
http_update_transfer(_, _, CgiHeader, none, CgiHeader).

join_transfer(chunked, chunked, chunked) :- !.
join_transfer(_, _, none).


%%	transfer(+Header, -Connection)
%	
%	Extract the desired connection from a header.

transfer(Header, Transfer) :-
	(   memberchk(transfer_encoding(Transfer0), Header)
	->  Transfer = Transfer0
	;   memberchk(http_version(1-X), Header),
	    X >= 1
	->  Transfer = chunked
	;   Transfer = none
	).


%%	content_length_in_encoding(+Encoding, +In, -Bytes)
%	
%	Determine hom much bytes are required to represent the data from
%	stream In using the given encoding.  Fails if the data cannot be
%	represented with the given encoding.

content_length_in_encoding(Enc, Stream, Bytes) :-
	open_null_stream(Out),
	set_stream(Out, encoding(Enc)),
	stream_property(Stream, position(Here)),
	(   catch((copy_stream_data(Stream, Out),
		   flush_output(Out)), _, fail)
	->  byte_count(Out, Bytes0)
	;   true
	),
	close(Out),
	set_stream_position(Stream, Here),
	(   var(Bytes0)
	->  fail
	;   Bytes = Bytes0
	).


		 /*******************************
		 *	    POST SUPPORT	*
		 *******************************/

%%	http_post_data(+Data, +Out:stream, +HdrExtra) is det.
%
%	Send data on behalf on an HTTP   POST request. This predicate is
%	normally called by http_post/4 from   http_client.pl to send the
%	POST data to the server.  Data is one of:
%	
%	  * html(+Tokens)
%	  Result of html//1 from html_write.pl
%	  
%	  * file(+File)
%	  Send contents of a file. Mime-type is determined by
%	  file_mime_type/2.
%	  
%	  * file(+Type, +File)
%	  Send file with content of indicated mime-type.
%	  
%	  * codes(+Codes)
%	  As string(text/plain, Codes).
%	  
%	  * codes(+Type, +Codes)
%	  Send Codes using the indicated MIME-type.
%	  
%	  * cgi_stream(+Stream, +Len)
%	  Read the input from Stream which, like CGI data starts with a partial
%	  HTTP header. The fields of this header are merged with the provided
%	  HdrExtra fields. The first Len characters of Stream are used.
%	  
%	  * form(+ListOfParameter)
%	  Send data of the MIME type application/x-www-form-urlencoded as
% 	  produced by browsers issuing a POST request from an HTML form.
%	  ListOfParameter is a list of Name=Value or Name(Value).
%	  
%	  * form_data(+ListOfData)
%	  Send data of the MIME type multipart/form-data.  ListOfData is the same
%	  as for the List alternative described below.
%	  
%	  * List
%	  If the argument is a plain list, it is sent using the MIME type
%	  multipart/mixed and packed using mime_pack/3. See mime_pack/3
%	  for details on the argument format.

:- multifile
	http_client:post_data_hook/3.

http_post_data(Data, Out, HdrExtra) :-
	http_client:post_data_hook(Data, Out, HdrExtra), !.
http_post_data(html(HTML), Out, HdrExtra) :-
	phrase(post_header(html(HTML), HdrExtra), Header),
	format(Out, '~s', [Header]),
	print_html(Out, HTML).
http_post_data(file(File), Out, HdrExtra) :- !,
	(   file_mime_type(File, Type)
	->  true
	;   Type = text/plain
	),
	http_post_data(file(Type, File), Out, HdrExtra).
http_post_data(file(Type, File), Out, HdrExtra) :- !,
	phrase(post_header(file(Type, File), HdrExtra), Header),
	format(Out, '~s', [Header]),
	open(File, read, In, [type(binary)]),
	call_cleanup(copy_stream_data(In, Out),
		     close(In)).
http_post_data(codes(Codes), Out, HdrExtra) :- !,
	http_post_data(codes(text/plain, Codes), Out, HdrExtra).
http_post_data(codes(Type, Codes), Out, HdrExtra) :- !,
	phrase(post_header(codes(Type, Codes), HdrExtra), Header),
	format(Out, '~s~s', [Header, Codes]).
http_post_data(cgi_stream(In, _Len), Out, HdrExtra) :- !,
	debug(obsolete, 'Obsolete 2nd argument in cgi_stream(In,Len)', []),
	http_post_data(cgi_stream(In), Out, HdrExtra).
http_post_data(cgi_stream(In), Out, HdrExtra) :- !,
	http_read_header(In, Header0),
	http_update_encoding(Header0, Encoding, Header),
	content_length_in_encoding(Encoding, In, Size),
	http_join_headers(HdrExtra, Header, Hdr2),
	phrase(post_header(cgi_data(Size), Hdr2), HeaderText),
	format(Out, '~s', [HeaderText]),
	set_stream(Out, encoding(Encoding)),
	call_cleanup(copy_stream_data(In, Out),
		     set_stream(Out, encoding(octet))).
http_post_data(form(Fields), Out, HdrExtra) :- !,
	parse_url_search(Codes, Fields),
	length(Codes, Size),
	http_join_headers(HdrExtra,
			  [ content_type('application/x-www-form-urlencoded')
			  ], Header),
	phrase(post_header(cgi_data(Size), Header), HeaderChars),
	format(Out, '~s', [HeaderChars]),
	format(Out, '~s', [Codes]).
http_post_data(form_data(Data), Out, HdrExtra) :- !,
	new_memory_file(MemFile),
	open_memory_file(MemFile, write, MimeOut),
	mime_pack(Data, MimeOut, Boundary),
	close(MimeOut),
	size_memory_file(MemFile, Size),
	format(string(ContentType), 'multipart/form-data; boundary=~w', [Boundary]),
	http_join_headers(HdrExtra,
			  [ mime_version('1.0'),
			    content_type(ContentType)
			  ], Header),
	phrase(post_header(cgi_data(Size), Header), HeaderChars),
	format(Out, '~s', [HeaderChars]),
	open_memory_file(MemFile, read, In),
	copy_stream_data(In, Out),
	close(In),
	free_memory_file(MemFile).
http_post_data(List, Out, HdrExtra) :-		% multipart-mixed
	is_list(List), !,
	new_memory_file(MemFile),
	open_memory_file(MemFile, write, MimeOut),
	mime_pack(List, MimeOut, Boundary),
	close(MimeOut),
	size_memory_file(MemFile, Size),
	format(string(ContentType), 'multipart/mixed; boundary=~w', [Boundary]),
	http_join_headers(HdrExtra,
			  [ mime_version('1.0'),
			    content_type(ContentType)
			  ], Header),
	phrase(post_header(cgi_data(Size), Header), HeaderChars),
	format(Out, '~s', [HeaderChars]),
	open_memory_file(MemFile, read, In),
	copy_stream_data(In, Out),
	close(In),
	free_memory_file(MemFile).

%%	post_header(+Data, +HeaderExtra)//
%
%	Generate the POST header, emitting HeaderExtra, followed by the
%	HTTP Content-length and Content-type fields.

post_header(html(Tokens), HdrExtra) -->
	header_fields(HdrExtra),
	content_length(html(Tokens)),
	content_type(text/html),
	"\r\n". 
post_header(file(Type, File), HdrExtra) -->
	header_fields(HdrExtra),
	content_length(file(File)),
	content_type(Type),
	"\r\n". 
post_header(cgi_data(Size), HdrExtra) -->
	header_fields(HdrExtra),
	content_length(Size),
	"\r\n". 
post_header(codes(Type, Codes), HdrExtra) -->
	header_fields(HdrExtra),
	content_length(ascii_string(Codes)),
	content_type(Type),
	"\r\n". 


		 /*******************************
		 *       OUTPUT HEADER DCG	*
		 *******************************/

%%	http_reply_header(+Out:stream, +What, +HdrExtra) is det.
%
%	Create a reply header  using  reply_header//2   and  send  it to
%	Stream.

http_reply_header(Out, What, HdrExtra) :-
	phrase(reply_header(What, HdrExtra), String), !,
	format(Out, '~s', [String]).
	

reply_header(string(String), HdrExtra) -->
	reply_header(string(text/plain, String), HdrExtra).
reply_header(string(Type, String), HdrExtra) -->
	vstatus(ok),
	date(now),
	header_fields(HdrExtra),
	content_length(ascii_string(String)),
	content_type(Type),
	"\r\n".
reply_header(html(Tokens), HdrExtra) -->
	vstatus(ok),
	date(now),
	header_fields(HdrExtra),
	content_length(html(Tokens)),
	content_type(text/html),
	"\r\n".
reply_header(file(Type, File), HdrExtra) -->
	vstatus(ok),
	date(now),
	modified(file(File)),
	header_fields(HdrExtra),
	content_length(file(File)),
	content_type(Type),
	"\r\n".
reply_header(tmp_file(Type, File), HdrExtra) -->
	vstatus(ok),
	date(now),
	header_fields(HdrExtra),
	content_length(file(File)),
	content_type(Type),
	"\r\n".
reply_header(cgi_data(Size), HdrExtra) -->
	vstatus(ok),
	date(now),
	header_fields(HdrExtra),
	content_length(Size),
	"\r\n".
reply_header(chunked_data, HdrExtra) -->
	vstatus(ok),
	date(now),
	header_fields(HdrExtra),
	(   {memberchk(transfer_encoding(_), HdrExtra)}
	->  ""
	;   transfer_encoding(chunked)
	),
	"\r\n".
reply_header(moved(To, Tokens), HdrExtra) -->
	vstatus(moved),
	date(now),
	header_field('Location', To),
	header_fields(HdrExtra),
	content_length(html(Tokens)),
	content_type(text/html, utf8),
	"\r\n".
reply_header(moved_temporary(To, Tokens), HdrExtra) -->
	vstatus(moved_temporary),
	date(now),
	header_field('Location', To),
	header_fields(HdrExtra),
	content_length(html(Tokens)),
	content_type(text/html, utf8),
	"\r\n".
reply_header(see_other(To,Tokens),HdrExtra) -->
	vstatus(see_other),
	date(now),
	header_field('Location',To),
	header_fields(HdrExtra),
	content_length(html(Tokens)),
	content_type(text/html, utf8),
	"\r\n".
reply_header(status(Status), HdrExtra) --> % Empty messages: 1xx, 204 and 304
	vstatus(Status),
	header_fields(HdrExtra),
	"\r\n".
reply_header(status(Status, Tokens), HdrExtra) -->
	vstatus(Status),
	date(now),
	header_fields(HdrExtra),
	content_length(html(Tokens)),
	content_type(text/html, utf8),
	"\r\n".
reply_header(authorise(Method, Realm, Tokens), HdrExtra) -->
	vstatus(authorise),
	date(now),
	authenticate(Method, Realm),
	header_fields(HdrExtra),
	content_length(html(Tokens)),
	content_type(text/html, utf8),
	"\r\n".

vstatus(Status) -->
	"HTTP/1.1 ",
	status_number(Status),
	" ",
	status_comment(Status),
	"\r\n".

%%	status_number(-Code)//
%
%	Parse the HTTP status numbers and return them as a code (atom).

status_number(continue)		   --> "100".
status_number(ok)		   --> "200".
status_number(moved)		   --> "301".
status_number(moved_temporary)	   --> "302".
status_number(see_other)	   --> "303".
status_number(not_modified)	   --> "304". 
status_number(not_found)	   --> "404".
status_number(forbidden)	   --> "403".
status_number(authorise)	   --> "401".
status_number(server_error)	   --> "500".
status_number(service_unavailable) --> "503".

status_comment(continue) -->
	"Continue".
status_comment(ok) -->
	"OK".
status_comment(moved) -->
	"Moved Permanently".
status_comment(moved_temporary) -->
	"Moved Temporary".
status_comment(see_other) -->
	"See Other".
status_comment(not_modified) --> 
	"Not Modified".
status_comment(not_found) -->
	"Not Found".
status_comment(forbidden) -->
	"Forbidden".
status_comment(authorise) -->
	"Authorization Required".
status_comment(server_error) -->
	"Internal Server Error".
status_comment(service_unavailable) -->
	"Service Unavailable".

authenticate(Method, '') --> !,
	"WWW-Authenticate: ",
	atom(Method).
authenticate(Method, Realm) -->
	authenticate(Method, ''),
	" Realm=\"", atom(Realm), "\"\r\n".

date(Time) -->
	"Date: ",
	(   { Time == now }
	->  now
	;   rfc_date(Time)
	),
	"\r\n".
	
modified(file(File)) --> !,
	{ time_file(File, Time)
	}, 
	modified(Time).
modified(Time) -->
	"Last-modified: ",
	(   { Time == now }
	->  now
	;   rfc_date(Time)
	),
	"\r\n".

content_length(ascii_string(String)) --> !,
	{ length(String, Len)
	},
	content_length(Len).
content_length(file(File)) --> !,
	{ size_file(File, Len)
	},
	content_length(Len).
content_length(html(Tokens)) --> !,
	{ html_print_length(Tokens, Len)
	},
	content_length(Len).
content_length(Len) -->
	{ number_codes(Len, LenChars)
	},
	"Content-Length: ", string(LenChars),
	"\r\n".

transfer_encoding(Encoding) -->
	"Transfer-Encoding: ", atom(Encoding), "\r\n".

content_type(Type) -->
	content_type(Type, _).

content_type(Type, Charset) -->
	ctype(Type),
	charset(Charset),
	"\r\n".

ctype(Main/Sub) --> !,
	"Content-Type: ",
	atom(Main),
	"/",
	atom(Sub).
ctype(Type) --> !,
	"Content-Type: ",
	atom(Type).

charset(Var) --> 
	{ var(Var) }, !.
charset(utf8) --> !,
	"; charset=UTF-8".
charset(CharSet) -->
	"; charset=",
	atom(CharSet).

header_field(Name, Value) -->
	{ var(Name) }, !,
	field_name(Name),
	":",
	whites,
	read_field_value(ValueChars),
	blanks_to_nl, !,
	{ field_to_prolog(Name, ValueChars, Value) }.
header_field(Name, Value) -->
	field_name(Name),
	": ",
	field_value(Value),
	"\r\n".

%%	read_field_value(-Codes)//
%
%	Read a field eagerly upto the next whitespace

read_field_value([H|T]) -->
	[H],
	{ \+ code_type(H, space) }, !,
	read_field_value(T).
read_field_value([]) -->
	"".
read_field_value([H|T]) -->
	[H],
	read_field_value(T).


field_to_prolog(content_length, ValueChars, ContentLength) :- !,
	number_codes(ContentLength, ValueChars).
field_to_prolog(cookie, ValueChars, Cookies) :- !,
	debug(cookie, 'Cookie: ~s', [ValueChars]),
	phrase(cookies(Cookies), ValueChars).
field_to_prolog(set_cookie, ValueChars, SetCookie) :- !,
	debug(cookie, 'SetCookie: ~s', [ValueChars]),
	phrase(set_cookie(SetCookie), ValueChars).
field_to_prolog(host, ValueChars, Host) :- !,
	(   append(HostChars, [0':|PortChars], ValueChars),
	    catch(number_codes(Port, PortChars), _, fail)
	->  atom_codes(HostName, HostChars),
	    Host = HostName:Port
	;   atom_codes(Host, ValueChars)
	).
field_to_prolog(_, ValueChars, Atom) :-
	atom_codes(Atom, ValueChars).

field_value(set_cookie(Name, Value, Options)) --> !,
	atom(Name), "=", atom(Value),
	set_cookie_options(Options).
field_value(Atomic) -->
	atom(Atomic).

set_cookie_options([]) -->
	[].
set_cookie_options([secure=true|T]) --> !,
	" ; secure",
	set_cookie_options(T).
set_cookie_options([Name=Value|T]) -->
	" ; ", field_name(Name), "=",
	atom(Value),
	set_cookie_options(T).


%	Process a sequence of [Name(Value), ...] attributes for the
%	header.

header_fields([]) -->
	[].
header_fields([H|T]) -->
	{ H =.. [Name, Value]
	},
	field_name(Name),
	whites,
	": ",
	field_value(Value),
	"\r\n",
	header_fields(T).

%%	field_name(?PrologName)
%
%	Convert between prolog_name and HttpName

field_name(Name) -->
	{ var(Name) }, !,
	rd_field_chars(Chars),
	{ atom_codes(Name, Chars) }.
field_name(mime_version) --> !,
	"MIME-Version".
field_name(Name) -->
	{ atom_codes(Name, Chars) },
	wr_field_chars(Chars).

rd_field_chars([C0|T]) -->
	[C],
	{ rd_field_char(C, C0) }, !,
	rd_field_chars(T).
rd_field_chars([]) -->
	[].

term_expansion(rd_field_char(_,_), Clauses) :-
	Clauses = [ rd_field_char(0'-, 0'_)
		  | Cls
		  ],
	findall(rd_field_char(In, Out),
		(   between(1, 127, In),
		    code_type(In, csym),
		    code_type(Out, to_lower(In))),
		Cls).

rd_field_char(_, _).


wr_field_chars([C|T]) -->
	[C2], !,
	{ to_lower(C2, C) },
	wr_field_chars2(T).
wr_field_chars([]) -->
	[].

wr_field_chars2([0'_|T]) --> !,
	"-",
	wr_field_chars(T).
wr_field_chars2([C|T]) --> !,
	[C],
	wr_field_chars2(T).
wr_field_chars2([]) -->
	[].

%	now
%%	rfc_date(+Time)

now -->
	{ get_time(Time)
	},
	rfc_date(Time).

%%	rfc_date(+Time)// is det.
%	
%	Write time according to RFC1123 specification as required by the
%	RFC2616 HTTP protocol specs. 

rfc_date(Time, String, Tail) :-
	stamp_date_time(Time, Date, 'UTC'),
	format_time(codes(String, Tail),
		    '%a, %d %b %Y %H:%M:%S GMT',
		    Date, posix).
	
%%	http_timestamp(+Time:timestamp, -Text:atom) is det.
%	
%	Generate a description of a Time in HTTP format (RFC1123)

http_timestamp(Time, Atom) :-
	stamp_date_time(Time, Date, 'UTC'),
	format_time(atom(Atom),
		    '%a, %d %b %Y %H:%M:%S GMT',
		    Date, posix).


		 /*******************************
		 *	   REQUEST DCG		*
		 *******************************/

request(Fd, [method(Method)|Header]) -->
	method(Method),
	blanks,
	nonblanks(Query),
	{ http_location(Parts, Query),
	  append(Parts, Header0, Header)
	},
	request_header(Fd, Header0), !.
request(Fd, [unknown(What)|Header]) -->
	string(What),
	eos, !,
	{   http_read_header(Fd, Header)
        ->  true
	;   Header = ""
	}.

method(get) -->
	"GET", !.
method(put) -->
	"PUT", !.
method(head) -->
	"HEAD", !.
method(post) -->
	"POST", !.

request_header(_, []) -->		% Old-style non-version header
	blanks,
	eos, !.
request_header(Fd, [http_version(Version)|Header]) -->
	http_version(Version),
	blanks,
	eos, !,
	{   Version = 1-_
	->  http_read_header(Fd, Header)
	;   Header = []
	}.

http_version(Version) -->
	blanks,
	"HTTP/",
	http_version_number(Version).

http_version_number(Major-Minor) -->
	integer(Major),
	".",
	integer(Minor).


		 /*******************************
		 *	      COOKIES		*
		 *******************************/

%	cookies are of the format NAME=Value; ...

cookies([Name=Value|T]) -->
	blanks,
	cookie(Name, Value), !,
	blanks,
	(   ";"
	->  cookies(T)
	;   { T = [] }
	).

cookie(Name, Value) -->
	cookie_name(Name),
	"=",
	cookie_value(Value).

cookie_name(Name) -->
	{ var(Name) }, !,
	rd_field_chars(Chars),
	{ atom_codes(Name, Chars) }.

cookie_value(Value) -->
	chars_to_semicolon_or_blank(Chars),
	{ atom_codes(Value, Chars)
	}.

chars_to_semicolon_or_blank([]) -->
	peek(0';), !.
chars_to_semicolon_or_blank([]) -->
	blank, !.
chars_to_semicolon_or_blank([H|T]) -->
	[H], !,
	chars_to_semicolon_or_blank(T).
chars_to_semicolon_or_blank([]) -->
	[].

peek(C, L, L) :-
	L = [C|_].

set_cookie(set_cookie(Name, Value, Options)) -->
	blanks,
	cookie(Name, Value),
	cookie_options(Options).

cookie_options([H|T]) -->
	blanks,
	";",
	blanks,
	cookie_option(H), !,
	cookie_options(T).
cookie_options([]) -->
	blanks.


cookie_option(secure=true) -->
	"secure", !.
cookie_option(Name=Value) -->
	rd_field_chars(NameChars), whites,
	"=", blanks,
	chars_to_semicolon(ValueChars),
	{ atom_codes(Name, NameChars),
	  atom_codes(Value, ValueChars)
	}.

chars_to_semicolon([]) -->
	blanks,
	peek(0';), !.
chars_to_semicolon([H|T]) -->
	[H], !,
	chars_to_semicolon(T).
chars_to_semicolon([]) -->
	[].


		 /*******************************
		 *	     REPLY DCG		*
		 *******************************/

%%	reply(+In, -Reply:list)// is semidet.
%
%	Process the first line of an HTTP   reply.  After that, read the
%	remainder  of  the  header  and    parse  it.  After  successful
%	completion, Reply contains the following fields, followed by the
%	fields produced by http_read_header/2.
%	
%	    * http_version(Major-Minor)
%	    * status(StatusCode, Comment)
%	    
%	StatusCode is one of the values provided by status_number//1.

reply(Fd, [http_version(HttpVersion), status(Status, Comment)|Header]) -->
	http_version(HttpVersion),
	blanks,
	(   status_number(Status)
	->  []
	;   integer(Status)
	),
	blanks,
	string(CommentCodes),
	blanks_to_nl, !,
	blanks,
	{ atom_codes(Comment, CommentCodes),
	  http_read_header(Fd, Header)
	}.


		 /*******************************
		 *	      READ HEADER	*
		 *******************************/

%%	http_read_header(+Fd, -Header) is det.
%
%	Read Name: Value lines from FD until an empty line is encountered.
%	Field-name are converted to Prolog conventions (all lower, _ instead
%	of -): Content-Type: text/html --> content_type(text/html)

http_read_header(Fd, Header) :-
	read_header_data(Fd, Text),
	http_parse_header(Text, Header).

read_header_data(Fd, Header) :-
	read_line_to_codes(Fd, Header, Tail),
	read_header_data(Header, Fd, Tail),
	debug(http(header), 'Header = ~n~s~n', [Header]).

read_header_data("\r\n", _, _) :- !.
read_header_data("\n", _, _) :- !.
read_header_data("", _, _) :- !.
read_header_data(_, Fd, Tail) :-
	read_line_to_codes(Fd, Tail, NewTail),
	read_header_data(Tail, Fd, NewTail).

http_parse_header(Text, Header) :-
	phrase(header(Header), Text),
	debug(http(header), 'Fields: ~w~n', [Header]).

header(List) -->
	header_field(Name, Value), !,
	{ mkfield(Name, Value, List, Tail)
	},
	blanks,
	header(Tail).
header([]) -->
	blanks,
	[].

%%	address//
%
%	Emit the HTML for the server address on behalve of error and
%	status messages (non-200 replies).  Default is
%
%	    ==
%	    SWI-Prolog httpd at <hostname>
%	    ==
%
%	The address can be modified by   providing  a definition for the
%	multifile predicate http:http_address//0.

:- multifile
	http:http_address//0.

address -->
	http:http_address, !.
address -->
	{ gethostname(Host) },
	html(address(['SWI-Prolog httpd at ', Host])).

mkfield(host, Host:Port, [host(Host),port(Port)|Tail], Tail) :- !.
mkfield(Name, Value, [Att|Tail], Tail) :-
	Att =.. [Name, Value].
