#!/usr/bin/env python
# python 3.6+

# THIS SCRIPT WAS AUTOGENERATIED FROM SOURCE FILES FOUND AT:
# https://github.com/Pristine-Cat/SymPad

# Copyright (c) 2019 Tomasz Pytel
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
#     * Redistributions of source code must retain the above copyright
#       notice, this list of conditions and the following disclaimer.
#     * Redistributions in binary form must reproduce the above copyright
#       notice, this list of conditions and the following disclaimer in the
#       documentation and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
# ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
# WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT HOLDER> BE LIABLE FOR ANY
# DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
# (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
# LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
# ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
# SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

_RUNNING_AS_SINGLE_SCRIPT = True


_FILES = {

	'style.css': # style.css

r"""* {
	box-sizing: border-box;
	margin: 0;
	padding: 0;
}

body {
	margin-top: 1em;
	margin-bottom: 6em;
	cursor: default;
}

#Clipboard {
	position: fixed;
	bottom: 0;
	color: transparent;
	border: 0px;
}

#Background {
	position: fixed;
	z-index: -1;
	left: 0;
	top: 0;
}

#Greeting {
	position: fixed;
	left: 50%;
	top: 50%;
	transform: translate(-50%, -50%);
	color: #0007;
}

.GreetingA {
	display: block;
	color: #0007;
	text-decoration: none;
	margin-bottom: 0.5em;
}

#InputBG {
	position: fixed;
	z-index: 2;
	height: 4em;
	bottom: 0;
	left: 0;
	right: 0;
	background-color: white;
}

#Input {
	position: fixed;
	z-index: 3;
	bottom: 2em;
	left: 4em;
	right: 1em;
	border-color: transparent;
	outline-color: transparent;
	background-color: transparent;
}

#InputOverlay {
	z-index: 4;
}

#OverlayGood {
	-webkit-text-fill-color: transparent;
}

#OverlayError {
	-webkit-text-fill-color: #f44;
}

#OverlayAutocomplete {
	-webkit-text-fill-color: #999;
}

.LogEntry {
	width: 100%;
	margin-bottom: 1.5em;
}

.LogMargin {
	display: inline-block;
	height: 100%;
	width: 4em;
	vertical-align: top;
	text-align: right;
	padding-right: 0.5em;
}

.LogBody {
	display: inline-block;
	margin-right: -9999em;
}

.LogWait {
	vertical-align: top;
}

.LogInput {
	margin-bottom: 0.75em;
	width: fit-content;
	cursor: pointer;
}

.LogEval {
	position: relative;
	margin-bottom: 0.25em;
	cursor: pointer;
}

.LogMsg {
	margin-bottom: 0.25em;
}

.LogError {
	margin-bottom: 0.25em;
	color: red;
}

.LogErrorTriange {
	position: absolute;
	left: -1.25em;
	top: 0.25em;
	font-size: 0.7em;
	color: red;
	font-weight: bold;
}
""".encode ("utf8"),

	'script.js': # script.js

r"""// TODO: clear() function to delete old log items.
// TODO: Change input to text field for longer expression support.
// TODO: Multiple spaces screw up overlay text position.
// TODO: Change how left/right arrows interact with autocomplete.
// TODO: Stupid scrollbars...
// TODO: Arrow keys in Edge?

URL              = '/';
MJQueue          = null;
MarginTop        = Infinity;
PreventFocusOut  = true;

LogIdx           = 0;
UniqueID         = 1;

Validations      = [undefined];
Evaluations      = [undefined];
ErrorIdx         = null;
Autocomplete     = [];

LastClickTime    = 0;
NumClicks        = 0;

GreetingFadedOut = false;

// replaced in env.js
History          = [];
HistIdx          = 0;
Version          = 'None'
DisplayStyle     = 1

//...............................................................................................
function generateBG () {
	function writeRandomData (data, x0, y0, width, height) {
		let p, d;

		for (let y = y0; y < height; y ++) {
			p = (width * y + x0) * 4;

			for (let x = x0; x < width; x ++) {
				d            = 244 + Math.floor (Math.random () * 12);
				data [p]     = data [p + 1] = d;
				data [p + 2] = d - 8;
				data [p + 3] = 255;
				p            = p + 4;
			}
		}
	}

	let canv    = document.getElementById ('Background');
	canv.width  = window.innerWidth;
	canv.height = window.innerHeight;
	let ctx     = canv.getContext ('2d');
	let imgd    = ctx.getImageData (0, 0, canv.width, canv.height); // ctx.createImageData (width, height);

	writeRandomData (imgd.data, 0, 0, canv.width, canv.height);
	ctx.putImageData (imgd, 0, 0);

	if (window.location.pathname == '/') {
		canv        = $('#InputBG') [0];
		ctx         = canv.getContext ('2d');
		canv.width  = window.innerWidth;

		ctx.putImageData (imgd, 0, 0);
	}
}

//...............................................................................................
function copyInputStyle () {
	JQInput.css ({left: $('#LogEntry1').position ().left})
	JQInput.width ($('#Log').width ());

	let style   = getComputedStyle (document.getElementById ('Input'));
	let overlay = document.getElementById ('InputOverlay');

  for (let prop of style) {
    overlay.style [prop] = style [prop];
	}

	overlay.style ['backgroundColor'] = 'transparent';
}

//...............................................................................................
function scrollToEnd () {
	window.scrollTo (0, document.body.scrollHeight);
}

//...............................................................................................
function resize () {
	copyInputStyle ();
	scrollToEnd ();
	generateBG ();
}

//...............................................................................................
function logResize () {
	// let atEnd  = !(document.documentElement.offsetHeight - document.documentElement.scrollTop - window.innerHeight);
	let margin = Math.max (BodyMarginTop, Math.floor (window.innerHeight - $('body').height () - BodyMarginBottom + 3)); // +3 is fudge factor

	if (margin < MarginTop) {
		MarginTop = margin
		$('body').css ({'margin-top': margin});
	}

	// if (atEnd) {
	// 	scrollToEnd ();
	// }
}

//...............................................................................................
var LastDocHeight = undefined;
var LastWinHeight = undefined;

function monitorStuff () {
	let curDocHeight = $(document).height ();
	let curWinHeight = $(window).height ();

	if (curDocHeight != LastDocHeight || curWinHeight != LastWinHeight) {
		copyInputStyle ();

		window.LastDocHeight = curDocHeight;
		window.LastWinHeight = curWinHeight;
	}

	if (PreventFocusOut) {
		JQInput.focus ();
	}

	setTimeout (monitorStuff, 50);
}

//...............................................................................................
function readyMathJax () {
	window.MJQueue = MathJax.Hub.queue;

	if (DisplayStyle) {
		var TEX        = MathJax.InputJax.TeX;
		var PREFILTER  = TEX.prefilterMath;

		TEX.Augment ({
			prefilterMath: function (tex, displaymode, script) {
				return PREFILTER.call (TEX, '\\displaystyle{' + tex + '}', displaymode, script);
			}
		});
	}
}

//...............................................................................................
function reprioritizeMJQueue () {
	let p = MJQueue.queue.pop ();

	if (p !== undefined) {
		MJQueue.queue.splice (0, 0, p);
	}
}

//...............................................................................................
function addLogEntry () {
	LogIdx += 1;

	$('#Log').append (`
			<div class="LogEntry"><div class="LogMargin">${LogIdx}.</div><div class="LogBody" id="LogEntry${LogIdx}"><div class="LogInput" id="LogInput${LogIdx}">
				<img class="LogWait" id="LogInputWait${LogIdx}" src="https://i.gifer.com/origin/3f/3face8da2a6c3dcd27cb4a1aaa32c926_w200.webp" width="16" style="visibility: hidden">
			</div></div></div>`)

	Validations.push (undefined);
	Evaluations.push (undefined);
}

//...............................................................................................
function writeToClipboard (text) {
	PreventFocusOut = false;

	$('#Clipboard').val (text);
	$('#Clipboard').focus ();
	$('#Clipboard').select ();
	document.execCommand ('copy');

	PreventFocusOut = true;

	JQInput.focus ();
}

//...............................................................................................
function copyToClipboard (e, val_or_eval, idx, subidx = 0) {
	let t = performance.now ();

	if ((t - LastClickTime) > 500) {
		NumClicks = 1;
	} else{
		NumClicks += 1;
	}

	LastClickTime = t;
	let resp      = val_or_eval ? Evaluations [idx].math [subidx] : Validations [idx];

	writeToClipboard (NumClicks == 1 ? resp.nat : NumClicks == 2 ? resp.py : resp.tex);

	e.style.color      = 'transparent';
	e.style.background = 'black';

	setTimeout (function () {
		e.style.color      = 'black';
		e.style.background = 'transparent';
	}, 100);
}

//...............................................................................................
function updateOverlay (text, erridx, autocomplete) {
	ErrorIdx     = erridx;
	Autocomplete = autocomplete;

	if (ErrorIdx === null) {
		$('#OverlayGood').text (text);
		$('#OverlayError').text ('');

	} else {
		$('#OverlayGood').text (text.substr (0, ErrorIdx));
		$('#OverlayError').text (text.substr (ErrorIdx));
	}

	$('#OverlayAutocomplete').text (Autocomplete.join (''));
}

//...............................................................................................
function ajaxResponse (resp) {
	if (resp.mode == 'validate') {
		if (Validations [resp.idx] !== undefined && Validations [resp.idx].subidx >= resp.subidx) {
			return; // ignore out of order responses (which should never happen with single threaded server)
		}

		if (resp.tex !== null) {
			Validations [resp.idx] = resp;

			let eLogInput = document.getElementById ('LogInput' + resp.idx);

			let queue              = [];
			[queue, MJQueue.queue] = [MJQueue.queue, queue];

			MJQueue.queue = queue.filter (function (obj, idx, arr) { // remove previous pending updates to same element
				return obj.data [0].parentElement !== eLogInput;
			})

			let eLogInputWait              = document.getElementById ('LogInputWait' + resp.idx);
			eLogInputWait.style.visibility = '';

			let idMath = 'LogInputMath' + UniqueID ++;
			$(eLogInput).append (`<span id="${idMath}" onclick="copyToClipboard (this, 0, ${resp.idx})" style="visibility: hidden">$${resp.tex}$</span>`);
			let eMath  = document.getElementById (idMath);

			MJQueue.Push (['Typeset', MathJax.Hub, eMath, function () {
				if (eMath === eLogInput.children [eLogInput.children.length - 1]) {
					eLogInput.appendChild (eLogInputWait);

					for (let i = eLogInput.children.length - 3; i >= 0; i --) {
						eLogInput.removeChild (eLogInput.children [i]);
					}

					eLogInputWait.style.visibility = 'hidden';
					eMath.style.visibility         = '';

					logResize ();
					scrollToEnd (); // ???
				}
			}]);

			reprioritizeMJQueue ();
		}

		updateOverlay (JQInput.val (), resp.erridx, resp.autocomplete);

	} else { // resp.mode == 'evaluate'
		Evaluations [resp.idx] = resp;

		let eLogEval = document.getElementById ('LogEval' + resp.idx);

		eLogEval.removeChild (document.getElementById ('LogEvalWait' + resp.idx));

		if (resp.err !== undefined) { // error?
			if (resp.err.length > 1) {
				let idLogErrorHidden = 'LogErrorHidden' + resp.idx;
				$(eLogEval).append (`<div id="${idLogErrorHidden}" style="display: none"></div>`);
				var eLogErrorHidden  = document.getElementById (idLogErrorHidden);

				for (let i = 0; i < resp.err.length - 1; i ++) {
					$(eLogErrorHidden).append (`<div class="LogError">${resp.err [i].replace (/  /g, '&emsp;')}</div>`);
				}
			}

			let idLogErrorTriangle = 'LogErrorTriangle' + resp.idx;
			$(eLogEval).append (`<div class="LogError">${resp.err [resp.err.length - 1]}</div><div class="LogErrorTriange" id="LogErrorTriangle${resp.idx}">\u25b7</div>`);
			var eLogErrorTriangle  = document.getElementById (idLogErrorTriangle);

			$(eLogEval).click (function () {
				if (eLogErrorHidden.style.display === 'none') {
					eLogErrorHidden.style.display = 'block';
					eLogErrorTriangle.innerText   = '\u25bd';
				} else {
					eLogErrorHidden.style.display = 'none';
					eLogErrorTriangle.innerText   = '\u25b7';
				}

				logResize ();
			});

			logResize ();
			scrollToEnd ();

		} else { // no error
			if (resp.math !== undefined && resp.math.length) { // math results present?
				for (let subidx in resp.math) {
					let idLogEvalDiv  = `LogEvalDiv${resp.idx}_${subidx}`;
					let idLogEvalMath = `LogEvalMath${resp.idx}_${subidx}`;

					$(eLogEval).append (`<div id="${idLogEvalDiv}" class="LogEval"><span id="${idLogEvalMath}" style="visibility: hidden" onclick="copyToClipboard (this, 1, ${resp.idx}, ${subidx})">$${resp.math [subidx].tex}$</span>
							<img id="LogEvalWait${resp.idx}_${subidx}" class="LogWait" src="https://i.gifer.com/origin/3f/3face8da2a6c3dcd27cb4a1aaa32c926_w200.webp" width="16">
							</div>`);

					let eLogEvalDiv   = document.getElementById (idLogEvalDiv);
					let eLogEvalMath  = document.getElementById (idLogEvalMath);

					MJQueue.Push (['Typeset', MathJax.Hub, eLogEvalMath, function () {
						eLogEvalDiv.removeChild (document.getElementById (`LogEvalWait${resp.idx}_${subidx}`));

						eLogEvalMath.style.visibility = '';

						logResize ();
						scrollToEnd ();
					}]);

					reprioritizeMJQueue ();
				}
			}

			if (resp.msg !== undefined && resp.msg.length) { // message present?
				for (let msg of resp.msg) {
					$(eLogEval).append (`<div class="LogMsg">${msg.replace (/  /g, '&emsp;')}</div>`);
				}

				logResize ();
				scrollToEnd ();
			}
		}
	}
}

//...............................................................................................
function inputting (text, reset = false) {
	if (reset) {
		ErrorIdx     = null;
		Autocomplete = [];

		JQInput.val (text);
	}

	updateOverlay (text, ErrorIdx, Autocomplete);

	$.ajax ({
		url: URL,
		type: 'POST',
		cache: false,
		dataType: 'json',
		success: ajaxResponse,
		data: {
			mode: 'validate',
			idx: LogIdx,
			subidx: UniqueID ++,
			text: text,
		},
	});
}

//...............................................................................................
function inputted (text) {
	$.ajax ({
		url: URL,
		type: 'POST',
		cache: false,
		dataType: 'json',
		success: ajaxResponse,
		data: {
			mode: 'evaluate',
			idx: LogIdx,
			text: text,
		},
	});

	$('#LogEntry' + LogIdx).append (`
			<div class="LogEval" id="LogEval${LogIdx}">
				<img class="LogWait" id="LogEvalWait${LogIdx}" src="https://i.gifer.com/origin/3f/3face8da2a6c3dcd27cb4a1aaa32c926_w200.webp" width="16">
			</div>`);

	History.push (text);

	HistIdx = History.length;

	addLogEntry ();
	logResize ();
	scrollToEnd ();
}

//...............................................................................................
function inputKeypress (e) {
	if (e.which == 13) {
		s = JQInput.val ().trim ();

		if ((s && ErrorIdx === null) || s === '?') {
			if (!GreetingFadedOut) {
				GreetingFadedOut = true;
				$('#Greeting').fadeOut (3000);
			}

			if (s === 'help' || s === '?') {
				window.open (`${URL}help.html`);
				inputting ('', true);

				return false;
			}

			if (Autocomplete.length > 0) {
				s = s + Autocomplete.join ('');
				inputting (s);
			}

			JQInput.val ('');
			updateOverlay ('', null, []);
			inputted (s);

			return false;
		}

	} else if (e.which == 32) {
		if (!JQInput.val ()) {
			return false;
		}
	}

	return true;
}

//...............................................................................................
function inputKeydown (e) {
	if (e.code == 'Escape') {
		e.preventDefault ();

		if (JQInput.val ()) {
			HistIdx = History.length;
			inputting ('', true);

			return false;
		}

	} else if (e.code == 'Tab') {
		e.preventDefault ();
		$(this).focus ();

		return false;

	} else if (e.code == 'ArrowUp') {
		e.preventDefault ();

		if (HistIdx) {
			inputting (History [-- HistIdx], true);

			return false;
		}

	} else if (e.code == 'ArrowDown') {
		e.preventDefault ();

		if (HistIdx < History.length - 1) {
			inputting (History [++ HistIdx], true);

			return false;

		} else if (HistIdx != History.length) {
			HistIdx = History.length;
			inputting ('', true);

			return false;
		}

	} else if (e.code == 'ArrowRight') {
		if (JQInput.get (0).selectionStart === JQInput.val ().length && Autocomplete.length) {
			let text = JQInput.val ();

			if (Autocomplete [0] === ' \\right') {
				text         = text + Autocomplete.slice (0, 2).join ('');
				Autocomplete = Autocomplete.slice (2);

			} else {
				text         = text + Autocomplete [0];
				Autocomplete = Autocomplete.slice (1);
			}

			JQInput.val (text);
			inputting (text);
			// updateOverlay (text, ErrorIdx, Autocomplete);
		}
	}
}

//...............................................................................................
// function inputFocusout (e) {
// 	if (PreventFocusOut) {
// 		e.preventDefault ();
// 		$(this).focus ();

// 		return false;
// 	}
// }

//...............................................................................................
$(function () {
	window.JQInput = $('#Input');

	if (window.location.pathname != '/') {
		generateBG ();
		return;
	}

	let margin       = $('body').css ('margin-top');
	BodyMarginTop    = Number (margin.slice (0, margin.length - 2));
	margin           = $('body').css ('margin-bottom');
	BodyMarginBottom = Number (margin.slice (0, margin.length - 2));

	$('#Clipboard').prop ('readonly', true);
	$('#InputBG') [0].height = $('#InputBG').height ();

	JQInput.keypress (inputKeypress);
	JQInput.keydown (inputKeydown);
	// JQInput.focusout (inputFocusout);
	// JQInput.blur (inputFocusout);

	addLogEntry ();
	logResize ();
	resize ();
	monitorStuff ();
});


// $('#txtSearch').blur(function (event) {
// 	setTimeout(function () { $("#txtSearch").focus(); }, 20);
// });

// document.getElementById('txtSearch').addEventListener('blur', e => {
//   e.target.focus();
// });

// cursor_test = function (element) {
// 	if (!element.children.length && element.innerText == '∥') {
// 		console.log (element, element.classList);
// 		element.innerText = '|';
// 		element.classList.add ('blinking');
// 	}

// 	for (let e of element.children) {
// 		cursor_test (e);
// 	}
// }

// cursor_test (eLogInput.children [0]);
""".encode ("utf8"),

	'index.html': # index.html

r"""<!DOCTYPE html>
<html>
<head>

<meta http-equiv="Content-Type" content="text/html; charset=utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, maximum-scale=1">
<meta http-equiv="X-UA-Compatible" content="IE=edge">
<link rel="icon" href="https://www.sympy.org/static/SymPy-Favicon.ico">
<title>SymPad</title>
<link rel="stylesheet" type="text/css" href="style.css">

<script type="text/javascript" src="https://code.jquery.com/jquery-3.4.1.js" integrity="sha256-WpOohJOqMqqyKL9FccASB9O0KwACQJpFTUBLTYOVvVU=" crossorigin="anonymous"></script>
<script type="text/javascript" src="script.js"></script>
<script type="text/javascript" src="env.js"></script>
<script type="text/x-mathjax-config">
	MathJax.Hub.Config ({
		messageStyle: "none",
		tex2jax: {inlineMath: [["$","$"], ["\\(","\\)"]]}
	});

	MathJax.Hub.Register.StartupHook ("End", readyMathJax);
</script>
<script type="text/javascript" src="https://cdnjs.cloudflare.com/ajax/libs/mathjax/2.7.5/latest.js?config=TeX-AMS_CHTML-full"></script>

</head>

<body onresize="resize ()">

<input id="Clipboard">
<canvas id="Background"></canvas>

<div id="Greeting">
	<div align="center">
		<h2>SymPad</h2>
		<h5><script type="text/javascript">document.write (Version)</script></h5>
		<br><br>
		Type '<b>help</b>' or '<b>?</b>' at any time for more information.
		<br>
		- or -
		<br>
		Type or click any of the following to get started:
	</div>
	<br><br>
	<a class="GreetingA" href="javascript:inputting ('cos**-1 x + \\log_2{8}', true)">cos**-1 x + \log_2{8}</a>
	<a class="GreetingA" href="javascript:inputting ('\\lim_{x\\to\\infty} 1/x', true)">\lim_{x\to\infty} 1/x</a>
	<a class="GreetingA" href="javascript:inputting ('Limit (\\frac1x, x, 0, dir=\'-\')', true)">Limit (\frac1x, x, 0, dir='-')</a>
	<a class="GreetingA" href="javascript:inputting ('\\sum_{n=0}**oo x^n / n!', true)">\sum_{n=0}**oo x^n / n!</a>
	<a class="GreetingA" href="javascript:inputting ('d**6 / dx dy**2 dz**3 x^3 y^3 z^3', true)">d**6 / dx dy**2 dz**3 x^3 y^3 z^3</a>
	<a class="GreetingA" href="javascript:inputting ('Derivative (\\int dx, x)', true)">Derivative (\int dx, x)</a>
	<a class="GreetingA" href="javascript:inputting ('Integral (e^{-x^2}, (x, 0, \\infty))', true)">Integral (e^{-x^2}, (x, 0, \infty))</a>
	<a class="GreetingA" href="javascript:inputting ('\\int_0^\\infty e^{-s t} dt', true)">\int_0^\infty e^{-s t} dt</a>
	<a class="GreetingA" href="javascript:inputting ('{{1,2},{3,4}}**-1', true)">{{1,2},{3,4}}**-1</a>
	<a class="GreetingA" href="javascript:inputting ('{{1,2,3},{4,5,6}}.transpose ()', true)">{{1,2,3},{4,5,6}}.transpose ()</a>
	<a class="GreetingA" href="javascript:inputting ('expand {x+1}**4', true)">expand {x+1}**4</a>
	<a class="GreetingA" href="javascript:inputting ('factor (x^3 + 3x^2 + 3x + 1)', true)">factor (x^3 + 3x^2 + 3x + 1)</a>
	<a class="GreetingA" href="javascript:inputting ('series (e^x, x, 0, 5)', true)">series (e^x, x, 0, 5)</a>
	<a class="GreetingA" href="javascript:inputting ('x if 1 &lt; 2 else y', true)">x if 1 &lt; 2 else y</a>
	<a class="GreetingA" href="javascript:inputting ('Matrix (4, 4, lambda r, c: c + r if c > r else 0)', true)">Matrix (4, 4, lambda r, c: c + r if c > r else 0)</a>

	<br><br>
	<div align="center">
	Copyright (c) 2019 Tomasz Pytel. <a href="https://github.com/Pristine-Cat/SymPad" target="_blank" style="color: #0007">SymPad on GitHub</a>
	</div>
</div>

<div id="Log"></div>

<canvas id="InputBG"></canvas>
<input id="Input" oninput="inputting (this.value)" autofocus>
<div id="InputOverlay"><span id="OverlayGood"></span><span id="OverlayError"></span><span id="OverlayAutocomplete"></span></div>

</body>
</html>""".encode ("utf8"),

	'help.html': # help.html

r"""<!DOCTYPE html>
<html>
<head>

<meta http-equiv="Content-Type" content="text/html; charset=utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, maximum-scale=1">
<link rel="icon" href="https://www.sympy.org/static/SymPy-Favicon.ico">
<title>SymPad Help</title>
<link rel="stylesheet" type="text/css" href="style.css">

<style>
	body { margin: 3em 4em; }
	h2 { margin: 2em 0 1em 0; }
	h4 { margin: 1.5em 0 0.5em 0; }
	p { margin: 0 0 1.2em 1em; line-height: 150%; }
	i { color: #0008; }
	del { color: red; }
</style>

<script type="text/javascript" src="https://code.jquery.com/jquery-3.4.1.js" integrity="sha256-WpOohJOqMqqyKL9FccASB9O0KwACQJpFTUBLTYOVvVU=" crossorigin="anonymous"></script>
<script type="text/javascript" src="script.js"></script>
<script type="text/javascript" src="env.js"></script>
<script type="text/x-mathjax-config">
	MathJax.Hub.Config ({
		messageStyle: "none",
		tex2jax: {inlineMath: [["$","$"], ["\\(","\\)"]]}
	});
</script>
<script type="text/javascript" src="https://cdnjs.cloudflare.com/ajax/libs/mathjax/2.7.5/latest.js?config=TeX-AMS_CHTML-full"></script>

</head>

<body onresize="generateBG ()">

<canvas id="Background"></canvas>

<h1 align="center" style="margin: 0">SymPad</h1>
<h4 align="center" style="margin: 0"><script type="text/javascript">document.write (Version)</script></h4>

<h2>Introduction</h2>

<p>
SymPad is a simple single script symbolic calculator / scratchpad using SymPy for the math and MathJax for the display in a browser.
It is a labor of love and grew out of a desire for an easy way to calculate a quick integral while studying some math without having to start a shell every time and import a package or fire up a browser and navigate to a site (technincally that last bit is exactly what happens but the response time is better :)
This desire for simplicity led to the single script option "sympad.py" which I could plop down on my desktop and execute when needed.
User input is intended to be quick, easy and intuitive and is displayed in symbolic form as it is being entered.
Sympad will accept Python expressions, LaTeX formatting, unicode math symbols and a native shorthand intended for quick entry, or a mix of all of these.
The input will be evaluated symbolically or numerically with the results being copy/pasteable in Python or LaTeX formats, so it acts as a translator as well.
</p>
<h4>Quick Start</h4>

<p>
The best way to see what SymPad can do is by doing, so try entering any of the following into SymPad:
</p><p>
cos**-1 x + \log_2{8}<br>
\lim_{x\to\infty} 1/x<br>
Limit (\frac1x, x, 0, dir='-')<br>
\sum_{n=0}**oo x^n / n!<br>
d**6 / dx dy**2 dz**3 x^3 y^3 z^3<br>
Derivative (\int dx, x)<br>
Integral (e^{-x^2}, (x, 0, \infty))<br>
\int_0^\infty e^{-s t} dt<br>
{{1,2},{3,4}}**-1<br>
{{1,2,3},{4,5,6}}.transpose ()<br>
expand {x+1}**4<br>
factor (x^3 + 3x^2 + 3x + 1)<br>
series (e^x, x, 0, 5)<br>
x if 1 &lt; 2 else y<br>
Matrix (4, 4, lambda r, c: c + r if c > r else 0)
</p>

<h4>Multiline examples</h4>

<p>
Enter the lines that follow one by one to see the effect:
</p><p>
1<br>
expand (_(x+1))<br>
expand (_(x+1))<i>&emsp;**(or press the up arrow)</i><br>
expand (_(x+1))<i>&emsp;...</i><br>
</p><p>
Or the following:
</p><p>
a, b = 1, 1<br>
a, b = b, a + b<br>
a, b = b, a + b<i>&emsp;**(or press the up arrow)</i><br>
a, b = b, a + b<i>&emsp;...</i><br>
</p><p>
Automatic variable substitution:
</p><p>
y = x**2 + 2x + 1<br>
y<br>
x = 2<br>
y<br>
</p>

<h4>Usage</h4>

<p>
You enter expresstions and they get evaluated.
The expressions may be in normal Pythonic style like "<b>a * (b + sin (x)**2 + 3/4) / 2</b>", LaTeX such as "<b>a\frac{b+\sin^2{x}+\frac34}{2}</b>" or a mix "<b>a * (b + \sin**x{2} + \frac34) / 2</b>".
The input is displayed symbolically as you type.
Input history is supported with the up and down arrows.
SymPad will give some limited options for autocompletion for certain expressions sometimes, this mostly means that you will not have to close parentheses.
</p><p>
The symbolic expressions can be copied to the clipboard in various formats.
Single-click for a simple native format meant to be pasted back into the input field.
A double click-copies the expression in Python format suitable for pasting into a Python shell or source file.
Finally, a triple-click will copy the expression in LaTeX format.
The single-click native and double-click Python formats should always be pasteable back into SymPad whereas the LaTeX format may or may not be depending on what elements are present.
</p><p>
SymPad normally allows long variable names, requires spaces between them for implicit multiplication and enforces grammatical breaks between function names and variables.
This can be turned off by switching into quick input mode using the function "<b>quick()</b>".
When in this mode long variable names are sacrificed for quicker input of single letter variables (Latin or Greek) and explicit space characters are no longer necessary between recognized function and variable names.
This means that an expression entered in normal mode like this "<b>x y sin z**2</b>" can be entered in quick mode like this "<b>xysinz**2</b>".
</p>

<h2>Types</h2>

<h4>Numbers</h4>

<p>
Numbers take the standard integer or floating point form or exponential form such as 123, -2.567, 1e+100, 3E-45 or -1.521e22.
The precision for all SymPy Floats used in evaluation is set to the highest precision number present in the equation, so if you ask for the cosine of a number with 50 decimal digits your answer will have at least 50 decimal digits.
</p><p>
Keep in mind that "<b>e</b>" or "<b>E</b>" is the Euler"s number constant $e$ and if you are trying to enter 2 times $e$ plus 22 then do not write it all together as "<b>2e+22</b>" as this will be interpreted to be "<b>2 * 10^22</b>".
Instead, use spaces and/or explicit multiplication: "<b>2 * e + 22</b>".
Imaginary numbers are entered using the imaginary unit "<b>i</b>" or "<b>I</b>" depending on preference, no Pythonic "<b>j</b>" option at the moment but it can be hacked by setting "<b>j = i</b>" in SymPad.
</p>

<h4>Variables</h4>

<p>
Variable names can be a mix of Python and LaTeX format, they can be multi-character but cannot start with an underscore "<b>_</b>" or a number though they may contain those.
Standard identifiers are accepted as well as single Greek letters optionally preceded by a slash such as "<b>\alpha</b>" ($\alpha$), "<b>epsilon</b>" ($\epsilon$) or "<b>\Psi</b>" ($\Psi$).
The Greek letters recognized and rendered in ... Greek ... are only those normally present within LaTeX which can not be visually confused with Latin letters.
Those Greek letters are accepted in unicode as well along with a few mathematical symbols (∞, ≠, ≤, ≥, ∂, ∑, ∫).
</p><p>
The variable names "<b>i</b>", "<b>e</b>" and "<b>\pi</b>" represent their respective mathematical constants $i$, $e$ and $\pi$.
"<b>pi</b>" and "<b>oo</b>" are also available for $\pi$ and $\infty$.
Python's "<b>None</b>", "<b>True</b>" and "<b>False</b>" are also present.
Variable names may be followed by various primes ' such as "<b> var' </b>" ($var'$) or "<b> \omega'' </b>" ($\omega''$).
By default, the lowercase "<b>e</b>" and "<b>i</b>" letters are used to represent Euler's number and the imaginary unit instead of the default SymPy uppercase "<b>E</b>" and "<b>I</b>".
This is objectively prettier, but can be changed via the "<b>sympyEI (True)</b>" and "<b>sympyEI (False)</b>" function.
The SymPy constant usage can also be activated via the command line switch "<b>--sympyEI</b>".
</p><p>
Differentials are entered as "<b>dx</b>", "<b>partialx</b>", "<b>\partialx</b>", "<b>\partial x</b>" or "<b>∂x</b>" and are treated as a single variable.
If you want to enter "<b>d</b>" * "<b>x</b>" multiplied implicitly then put a space between them or two spaces between the "<b>\partial</b>" and the "<b>x</b>".
There is nothing special about differential variables other than their specific use in differentiation and integration.
</p><p>
Variables may be assigned values, references to other variables or even entire expressions which will subsequently be substituted for those variables in any future expression evaluation.
They may also be assigned a user function which allows you to use them as macro expression functions, that is covered in the section on functions.
</p>

<h4>Vectors and Matrices</h4>

<p>
These are specified using curly braces with commas.
Vectors are passed as a single level of curlys such as "<b>{1, 2}</b>" or "<b>{x, y, z}</b>" and these are interpreted as column matrices.
Matrices are passed as nested rows of curlys.
A 2x3 matrix would be specified as  "<b>{{1, 2, 3}, {4, 5, 6}}</b>", a 1x3 would be "<b>{{1, 2, 3},}</b>" and a 3x1 would be either "<b>{{1,}, {2,}, {3,}}</b>" or just "<b>{1, 2, 3}</b>" since this is equivalent.
Note the trailing commas which are needed for the same reason as in Python for tuples of one element (otherwise the curlys would be treated as parenteses instead of vectors / matrices).
These can also be entered using LaTeX "<b>\<span></span>begin{(v|b|p|)matrix} \<span></span>end{(v|b|p|)matrix}</b>" format.
</p>

<h4>Piecewise Expressions</h4>

<p>
These are supported and can be entered as SymPy "<b>Piecewise</b>" functions, LaTeX "<b>\<span></span>begin{cases} \<span></span>end{cases}</b>" notation or the native Python-like conditional expressions of the form "<b>a if condition else b</b>".
They may be arbitrarily long - "<b>a if condition1 else b if condition2 else ...</b>" and may leave off the last "<b>else</b>" which is equivalent to a SymPy "<b>Piecewise</b>" function without a terminating "<b>True</b>" condition.
</p>

<h4>Strings</h4>

<p>
These exist for the sole purpose of passing string hints or other arguments to SymPy functions. They work as expected being enclosed by single or double quotes and
supporting escape sequences. For example "<b>Limit (1/x, x, 0, '-')</b>".
</p>

<h4>Lists and Tuples</h4>

<p>
Standard Python bracket enclosed lists and optionally parentheses enclosed tuples are accepted.
Like strings these exist for the purpose of passing parameters to functions like "<b>Matrix ([[1,2],[3,4]])</b>".
</p>

<h2>Operations</h2>

<h4>Addition and Multiplication</h4>

<p>
Addition is addition and subtraction is subtraction: "<b>a + b</b>", "<b>a - b</b>".
Multiplication is explicit with a "<b>*</b>" operator or implicit simply by writing two symbols next to each other with a space in between so that "<b>a * b</b>" is the same as "<b>a b</b>".
There is however a difference between the two in that the implicit version has a higher precedence than the explicit, which means that explicit multiplication will end a limit, sum, derivative or division "<b>/</b>" expression whereas implicit multiplication will not, e.g. "<b>1/x y</b>" = $\frac{1}{x y}$ whereas "<b>1/x*y</b>" = $\frac{1}{x} \cdot y$.
</p><p>
Division also has two operators, the normal "<b>/</b>" which has a fairly low precedence and the LaTeX "<b>\frac</b>" version which has a very high precedence, even higher than exponentiation.
So high in fact that parentheses are not needed if using "<b>\frac</b>" as an exponent as in "<b>x^\frac{1}{2}</b>" = $x^\frac{1}{2}$.
The "<b>\frac</b>" operation also does not need parentheses if using single digit operands or single letter variables (Latin or Greek) such as "<b>\frac12</b>" = $\frac12$ or "<b>\frac\alpha\beta</b>" = $\frac\alpha\beta$.
</p>

<h4>Exponentiation</h4>

<p>
There are two power opearators "<b>^</b>" and "<b>**</b>". They have the same precedence and can be used interchangeably but follow slightly different
parsing rules. The "<b>^</b>" operator follows LaTeX rules which only allow a single positive digit or letter variable (Lating or Greek) without the use
of curly braces whereas the "<b>**</b>" follows Python rules which allow negative values or variables or functions. To illustrate the diffference:
"<b>x**-2</b>" = $x^{-2}$ whereas "<b>x^-2</b>" = $x^-2$ (which makes no sense). Also, "<b>e**ln(x)</b>" will work as expected $e^{\ln(x)}$ whereas
"<b>e^ln(x)</b>" = $e^ln(x)$.
</p>

<h4>Logarithms</h4>

<p>
The natural logarithm of x is specified by "<b>lnx</b>", "<b>\ln x</b>", "<b>log x</b>", "<b>\log{x}</b>". A logarithm in a specific base is specified
by "<b>\log_b x</b>" = $\log_b x$, "<b>\log_{10}(1000)</b>" = $\log_{10} {1000}$ = 3, etc...
</p>

<h4>Roots</h4>

<p>
The square root of x ($\sqrt{x}$) may be entered in any of these forms "<b>sqrtx</b>", "<b>\sqrt x</b>", "<b>sqrt (x)</b>", "<b>\sqrt{x}</b>", with or without the slash.
The cube (or any other) root is similar, $\sqrt[3]x$ = "<b>sqrt[3]x</b>", "<b>sqrt[3] (x)</b>" or "<b>\sqrt[3] {x}</b>".
</p>

<h4>Factorial</h4>

<p>
"<b>4!</b>" = "<b>24</b>", "<b>x!</b>" = "<b>factorial(x)</b>", "<b>(-0.5)!</b>" = "<b>1.77245385090552</b>" and "<b>simplify(x!/x)</b>" = "<b>gamma(x)</b>".
</p>

<h4>Limits</h4>

<p>
To take the limit of an expression "<b>z</b>" as variable "<b>x</b>" approaches "<b>y</b>" enter "<b>\lim_{x \to y} (z)</b>" = $\lim_{x\to y} (z)$.
This will only give the limit if it exists and is the same when approaching from both directions, unlike SymPy which defaults to approaching from the
positive direction. To specify a direction add "<b>^+</b>" or "<b>^-</b>" to the equation as such: "<b>\lim_{x \to 0^+} 1/x</b>" = $\lim_{x\to 0^+}
\frac1x$ = $\infty$ and "<b>\lim_{x \to 0^-} 1/x</b>" = $\lim_{x\to 0^-} \frac1x$ = $-\infty$. Addition and explicit multiplication terminate a limit
expression. Limits may also be entered using the standard SymPy syntax "<b>Limit (expression, variable, to)</b>", this defaults to limit from positive
direction like SymPy, or you may specify a direction "<b>Limit (expression, variable, to, dir='+-')</b>".
</p>

<h4>Sums</h4>

<p>
The summation (finite or infinite) of expression "<b>z</b>" as variable "<b>n</b>" ranges from "<b>a</b>" to "<b>b</b>" is written as "<b>\sum_{n=a}^b
(z)</b>" = $\sum_{n=a}^b (z)$. Iterated sums work as expected, "<b>\sum_{n=1}^3 \sum_{m=1}^n m</b>" = $\sum_{n=1}^3 \sum_{m=1}^n m$ = 10. Addition and
explicit multiplication terminate a sum expression.
Sums may also be entered using the standard SymPy syntax "<b>Sum (expression, (variable, from, to))</b>".
</p>

<h4>Differentiation</h4>

<p>
The derivative of expression "<b>z</b>" with respect to "<b>x</b>" is entered as "<b>d/dx z</b>" or "<b>\frac{d}{dx} z</b>" = $\frac{d}{dx} z$. The
second derivative is "<b>d^2/dx^2 (z)</b>" or "<b>\frac{d^2}{dx^2} (z)</b>" = $\frac{d^2}{dx^2} (z)$. Using "<b>\partial</b>" ($\partial$) is allowed but
must be consistent within the expression. Mixed derivatives are entered as "<b>d^2 / dx dy (z)</b>" or "<b>\partial^2 / \partial x\partial y (z)</b>" =
$\frac{\partial^2}{\partial x\partial y} (z)$. Derivatives may also be entered using the standard SymPy syntax "<b>Derivative (expression, var1, var2,
power2, ...)</b>".
</p>

<h4>Integration</h4>

<p>
The anti-derivative of expression "<b>z</b>" with respect to x is written as "<b>\int z dx</b>" = $\int z\ dx$. The definite integral from "<b>a</b>" to
"<b>b</b>" is "<b>\int_a^b z dx</b>" = $\int_a^b z\ dx$. "<b>\int dx/x</b>" = $\int \frac1x\ dx$. Iterated and improper integrals also work. Integrals
may also be entered using the standard SymPy syntax "<b>Integral (expression, (variable, from, to))</b>".
</p>

<h4>(In)equalities</h4>

<p>
Are parsed from the standard Python "<b>=, ==, !=, &lt;, &lt;=, &gt;, &gt;=</b>" or LaTeX "<b>\ne, \neq, \lt, \le, \gt, \ge</b>" symbols.
Currently only a single comparison is allowed so an expression like "<b>0 &lt;= x &lt;= 2</b>" is not valid.
Note that the "<b>=</b>" and "<b>==</b>" operators are equivalent for SymPy and mapped to the same "<b>Eq</b>" object in expressions but the single "<b>=</b>" operator has a lower precedence than the others and is used by SymPad for variable assignment whereas the double "<b>==</b>" only ever implies comparison.
</p>

<h4>Indexing</h4>

<p>
Python style bracket indexing is natively supported for all objects using single or tuple indices, no slices yet - "<b>{{1, 2, 3}, {4, 5, 6}} [1,2] == 6</b>".
</p>

<h4>Parentheses</h4>

<p>
Explicit "<b>( )</b>" or implicit curly "<b>{ }</b>" parentheses allow prioritization of lower precedence operations over higher ones as usual and also
delineate an expression as an input to a function. They may be used interchangeably for single expressions, the only difference being that the implicit
version is not drawn if it does not need to be. The case where explicit "<b>( )</b>" parentheses are needed ... explicitly ... is when calling functions
in general and always when calling functions which take multiple parameters like "<b>max(1,2,3)</b>". The curly braces are used as shorthand for vectors
and matrices if commas are present, but that is a different syntactic usage, curlys with no commas are essentially invisible parentheses.
</p>

<h4>Member Access</h4>

<p>
You can access member data or functions of an expression just like in Python with the "<b>.</b>" operator.
If the attribute name following the dot is followed by a parenthesized expression then it will be treated as a function call instead of an implicit multiplication, otherwise it is a data member.
For example, two ways to get the transpose of a matrix are "<b>{{1,2,3},{4,5,6}}.T</b>" and "<b>{{1,2,3},{4,5,6}}.transpose ()</b>".
</p>

<h4>Variable Assignment</h4>

<p>
Using the syntax "<b>var = expression</b>" you can assign some value to be substituted for that variable in all expressions.
For example, doing "<b>x = pi</b>" and then evaluating "<b>cos x</b>" will give you "<b>-1</b>".
Anything can be assigned to any valid variable like mathematical expressions, Python objects like strings or lists, user lambda functions or even references to other variables.
To delete an assignment use the "<b>del var</b>" function, to delete all non-lambda variables do "<b>delvars</b>", to delete all assignments (including lambdas) use "<b>delall</b>".
To see what variables are currently assigned to, use the "<b>vars</b>" function.
This will not show lambda assignments though, to see those use "<b>funcs</b>".
</p><p>
Tuple assignment is supported and as in Python the source can be another tuple or a single iterable object like "<b>x, y = 1, 2</b>".
A useless example of iterable assignment would be setting "<b> a, b, c = 'str' </b>" which would give you "<b> a = 's' </b>", "<b> b = 't' </b>" and "<b> c = 'r' </b>".
</p><p>
There are two distinct types of assignment that can occur and you should be aware of the difference between them.
Copy assignment is the standard type of assignment used by default in most computer languages where if you start with "<b>x = 1</b>" and you then enter "<b>y = x</b>" then the value "<b>1</b>" will be copied to the "<b>y</b>" variable.
The value of "<b>y</b>" will be independent of whatever else happens to the variable "<b>x</b>" after this.
</p><p>
The other kind of assignment is a reference assignment which will map the source variable instead of copying its value to the target.
This means that if you have a reference set like "<b>y = x</b>" and the value of "<b>x</b>" changes then the value of "<b>y</b>" will reflect this new value as well.
The reference assignment happens if you try to assign variables which do not exist, so setting "<b>y = x</b>" before "<b>x</b>" has been created will result in a reference.
Otherwise you can force a reference by using the "<b>@()</b>" pseudo-function.
Doing "<b>y = @x</b>" will create a reference to "<b>x</b>" itself instead of copying the value if it exists.
The "<b>@(expr)</b>" function technically prevents variable remapping for the expression it encompasses, so if you have the variable "<b>x = 2</b>" set and you do "<b>@(x)</b>" then you will get "<b>x</b>" and not "<b>2</b>".
</p>

<h2>Functions</h2>
<p>
There are two types of functions made available in SymPad - all the SymPy native functions are available directly just by typing their name (a few escaped with "<b>$</b>"), as well as user created lambda functions assigned to variables.
In addition, member functions of objects are supported and callable like "<b>Matrix ([1,2,3]).transpose ()</b>".
All functions may take multiple comma-separated arguments and the SymPy functions also optionally take keyword arguments.
</p>

<h4>SymPy Functions</h4>

<p>
Almost all SymPy function and objects from the top level of the SymPy module are made available directly for calling by their name like "<b>tan(x)</b>", the only restriction being they must be longer than a single character and may not begin with an underscore.
This means no "<b>N()</b>", "<b>S()</b>" or "<b>O()</b>" directly, though those and functions and others beginning with an underscore as well as many __builtins__ can still be accessed with the "<b>$</b>" function override escape character, for example "<b>$oct (10)</b>".
Only the "safe" __builtin__ functions are specifically made available, functions like "<b>eval</b>", "<b>exec</b>" and many more have been left out and are not accessible.
To numerically evaluate the value of "<b>sin (2)</b>" you use the "<b>$</b>" escape character with the "<b>N()</b>" function like "<b>$N (sin (2))</b>", or just use the member function "<b>sin (2).evalf ()</b>".
</p><p>
The standard trigonometric and hyperbolic functions and their inverses can be entered as usual, the forward functions with or without a leading slash: "<b>sin</b>", "<b>\coth</b>".
The inverses are entered as Pythonic functions without a slash like "<b>atan</b>" or "<b>acscsh</b>" and the LaTeX versions take a slash and and are spelled out "<b>\arctan</b>".
The inverses may also be specified using the common mathematical syntax: "<b>\tan^{-1}x</b>" or "<b>cos**-1 x</b>".
This form of exponentiating a function is extended as an input shortcut to all top-level functions so that typing "<b>ln**2x</b>" is a quick way to enter "<b>(ln(x))**2</b>".
This does not apply to member functions or user created lambda functions.
Keep in mind that the "<b>-1</b>" exponent in this context is just a -1 and does not specify the inverse function as it does for the forward trigonometric and hyperbolic functions.
</p><p>
Top-level functions also don't require explicit parentheses in order to allow quick entry like "<b>sqrt 2</b>" or "<b>sin**-1x</b>" but for any parameter more complicated than another function or variable to a power they will be needed.
Functions which take zero or more than one single parameter, as well as member functions such as "<b>{{1, 1}, {0, 1}}.det()</b>" and lambdas always require explicit parentheses.
Many functions which have a common mathematical display style are translated on the fly for rendering in that style.
These include the functions "<b>abs/Abs (x)</b>" which are rendered as the standard bar syntax for absolute value "<b>|x|</b>", the "<b>factorial (x)</b>" function becomes "<b>x!</b>" and "<b>exp (x)</b>" displays as "<b>e^x</b>".
Some other functions which are translated are "<b>Derivative</b>", "<b>diff</b>", "<b>Integral</b>", "<b>integrate</b>", "<b>Limit</b>", "<b>limit</b>", "<b>Matrix</b>", "<b>Piecewise</b>", "<b>pow</b>", "<b>Pow</b>" and "<b>Sum</b>", and more...
</p>

<h4>Lambda Functions</h4>

<p>
User created lambda functions are supported and are specified the same way as Python lambdas - "<b>lambda x, y: (x+y)**2</b>".
In order to make use of them though you must assign them to a variable like "<b>f = lambda x: x**2</b>", now when you call "<b>f(3)</b>" you will get "<b>9</b>" as the result.
When created, lambda functions will copy the global value of any variables which are not lambda arguments and this will be fixed for the life of the lambda.
If you want a lambda to use the value of a global variable at the time the lambda is evaluated, rather than when it is defined, then wrap the instance of the variable in the lambda using the "<b>@()</b>" pseudo-function.
Lambda functions may reference other lambda functions as long as those are defined at the time of creation.
Lambda recursion is currently not supported.
</p><p>
Normally when you enter an expression into SymPad and hit Enter that expression is evaluated and "<b>doit()</b>" is called on it to attempt to symbolically evaluate an answer.
This may not always be desirable, like maybe in a lambda function, since when you enter a lambda function it is evaluated before it is assigned to a variable.
This means that if you do "<b>f = lambda x: \int x dx</b>" you will wind up with a lambda function which is equivalent to "<b>f = lambda x: 1/2 x**2</b>" instead of the integral expression.
In order to prevent evaluation of the integral on assignment and embed the operation itself within the lambda use the "<b>%()</b>" stop evaluation pseudo-function.
This function essentially defers evaluation of an expression for one round.
This will result in an assignment of "<b>f = lambda x: \int x dx</b>" if you define it as "<b>f = lambda x: %(\int x dx)</b>" instead of the result of the integral and this integral itself will be evaluated any time the lambda function is invoked.
</p><p>
This pseudo-function takes an optional count as a second argument.
The default count is 1 round of evaluation, but you may set it to 2 or more to defer evaluation for that many rounds, though I'm not sure if a finite count would be useful for anything.
What could be useful is a count of infinity, this would freeze the expression as it is and never evaluate.
</p>

<h4>Functions, Parentheses and Implicit Multiplication</h4>

<p>
SymPad supports implicit multiplication, that is writing two variables next to each other to indicate multiplication so "<b>x y</b>" = "<b>x * y</b>".
This brings some problems, such as deciding when "<b>x (a)</b>" is a function call and when it is multiplication.
SymPad solves this by recognizing all top-level SymPy package function names and classes as functions and accepting the next expression as the argument(s) to that function.
This brings along its own set of peculiarities such as removing those names from the possible namespace pool of variables, this means that you can never redefine "<b>sin</b>" as anything else, but why would you want to?
</p><p>
This recognition only works on top-level objects, for members of an object the presence of a parenthesized expression after the attribute name will imply a function call.
If that is not the intent and you instead want to treat the member as a data variable and multiply it with something then you must use explicit "<b>*</b>" multiplication or the curly parentheses as such "<b>{1, 2, 3}.T * (a + b)</b>" or "<b>{1, 2, 3}.T {a + b}</b>".
If you try to do this with regular parentheses then a function call will be attempted with "<b>a + b</b>" as the argument.
The meaning of parentheses for assigned user variables is inferred from whether the variable is a lambda or not, for lambdas parentheses are a function call and for other types they indicate multiplication.
</p><p>
In a roundabout sort of way this all led to a peculiar delima.
There is a namespace collision between the Greek letters "<b>beta</b>", "<b>zeta</b>", "<b>Gamma</b>" and "<b>Lambda</b>" and SymPy functions with those names (well, lowercase SymPy gamma() really, but it is represented normally with the uppercase letter).
This means that those function names could be encoded in the grammar and never be available for use as free variables, or they could be excluded from the grammar forcing the user to call them each time using the function escape character "<b>$</b>".
This was not very elegant so a workaround has been implemented as follows:
The function names have been left out of the grammar but user lambdas are created for them on startup so that they may be used as functions.
If you wish to use those letters as variables instead then simply delete the defined lambdas and those letters will behave as variables once more.
You can always redefine the lambdas yourself if you want them back, the format is as follows - "<b>beta = lambda x, y: %$beta (x, y)</b>".
</p>

<h2>Notes</h2>

<p>
<b>WARNING!</b> This http server implementation is nowhere near secure, this as well as the posibility of execution of arbitrary Python functions means you should never leave this server open to the internet by serving on an IP address visible to the external world.
</p><p>
There is a special use for the "<b>_</b>" underscore character which is the same as in the Python interactive shell in that it represents the last expression successfully evaluated.
To see this in action type in "<b>1</b>" and hit Enter, then type in "<b>expand ((x+1)*_)</b>" and hit Enter.
Repeat this several times using the up arrow.
</p><p>
After filling up the browser with many pretty mathematical expressions you may note that it starts to get slower, simply reload the page, all your variables and history will be preserved.
Or try adding "<b>--ugly</b>" to the command line, this will use a quicker draft rendering for the math.
</p><p>
Due to mixing operators from Python and LaTeX the grammar may be a little wonky in places so if something doesn't seem to work as it should try wrapping it in parentheses or putting a space between the problematic elements.
</p><p>
You can always tell whether SymPad will treat an identifier as a function or a variable by looking at the font which is used for the name, it is different for functions vs. variables.
Also, SymPad will give you an empty set of parentheses as an autocomplete option when it recognizes a function name (this only works for top-level functions).
</p><p>
If you are getting results which are just plain wrong, check to see if you have any variables mapped which would be changing the evaluation.
</p><p>
SymPad inserts the current working directory at the beginning of the Python module search path which means that for example if you run SymPad in the SymPy development directory then the SymPy module used will be the development version.
</p><p>
The server runs a single thread for consistency and keeps a single global state (variables), this means that if have two browser windows open the results of calculations in one will be reflected in the other.
</p><p>
There are many SymPy objects which SymPad does not understand natively yet.
In any case where such an object is the result of an evalutation then the SymPy LaTeX representation will be used for the displayed answer and the SymPy str version of the element will be used in the native representation string.
This should allow you to continue working with the calculation.
</p>

<br><br>
<div align="center">
Copyright (c) 2019 Tomasz Pytel, All rights reserved.

SymPad on GitHub: <a target="_blank" href="https://github.com/Pristine-Cat/SymPad">https://github.com/Pristine-Cat/SymPad</a>
</div>

</body>
</html>""".encode ("utf8"),
}

import re
import types

#...............................................................................................
class Incomplete (Exception):
	def __init__ (self, red):
		self.red = red

class Token (str):
	def __new__ (cls, str_, text = None, pos = None, grps = None):
		self      = str.__new__ (cls, str_)
		self.text = text or ''
		self.pos  = pos
		self.grp  = () if not grps else grps

		return self

class State (tuple): # easier on the eyes
	def __new__ (cls, *args):
		return tuple.__new__ (cls, args)

	def __init__ (self, *args): # idx = state index, sym = symbol (TOKEN or 'expression'), red = reduction (if present)
		if len (self) == 2:
			self.idx, self.sym = self
		else: # must be 3
			self.idx, self.sym, self.red = self

class Parser:
	_PARSER_TABLES = '' # placeholders so pylint doesn't have a fit
	_PARSER_TOP    = ''
	TOKENS         = {}

	_rec_SYMBOL_NUMTAIL = re.compile (r'(.*[^_\d])(_?\d+)?') # symbol names in code have extra digits at end for uniqueness which are discarded

	def set_tokens (self, tokens):
		self.tokgrps = {} # {'token': (groups pos start, groups pos end), ...}
		tokpats      = list (tokens.items ())
		pos          = 0

		for tok, pat in tokpats:
			l                   = re.compile (pat).groups + 1
			self.tokgrps [tok]  = (pos, pos + l)
			pos                += l

		self.tokre   = '|'.join (f'(?P<{tok}>{pat})' for tok, pat in tokpats)
		self.tokrec  = re.compile (self.tokre)

	def __init__ (self):
		if isinstance (self._PARSER_TABLES, bytes):
			import ast, base64, zlib
			symbols, rules, strules, terms, nterms = ast.literal_eval (zlib.decompress (base64.b64decode (self._PARSER_TABLES)).decode ('utf8'))
		else:
			symbols, rules, strules, terms, nterms = self._PARSER_TABLES

		self.set_tokens (self.TOKENS)

		self.rules   = [(0, (symbols [-1]))] + [(symbols [r [0]], tuple (symbols [s] for s in (r [1] if isinstance (r [1], tuple) else (r [1],)))) for r in rules]
		self.strules = [[t if isinstance (t, tuple) else (t, 0) for t in (sr if isinstance (sr, list) else [sr])] for sr in strules]
		states       = max (max (max (t [1]) for t in terms), max (max (t [1]) for t in nterms)) + 1
		self.terms   = [{} for _ in range (states)] # [{'symbol': [+shift or -reduce, conflict +shift or -reduce or None], ...}] - index by state num then terminal
		self.nterms  = [{} for _ in range (states)] # [{'symbol': +shift or -reduce, ...}] - index by state num then non-terminal
		self.rfuncs  = [None] # first rule is always None

		for t in terms:
			sym, sts, acts, confs = t if len (t) == 4 else t + (None,)
			sym                   = symbols [sym]

			for st, act in zip (sts, acts):
				self.terms [st] [sym] = (act, None)

			if confs:
				for st, act in confs.items ():
					self.terms [st] [sym] = (self.terms [st] [sym] [0], act)

		for sym, sts, acts in nterms:
			for st, act in zip (sts, acts):
				self.nterms [st] [symbols [sym]] = act

		prods = {} # {('production', ('symbol', ...)): func, ...}

		for name in dir (self):
			obj = getattr (self, name)

			if name [0] != '_' and type (obj) is types.MethodType and obj.__code__.co_argcount >= 1: # 2: allow empty productions
				m = Parser._rec_SYMBOL_NUMTAIL.match (name)

				if m:
					parms = tuple (p if p in self.TOKENS else Parser._rec_SYMBOL_NUMTAIL.match (p).group (1) \
							for p in obj.__code__.co_varnames [1 : obj.__code__.co_argcount])
					prods [(m.group (1), parms)] = obj

		for irule in range (1, len (self.rules)):
			func = prods.get (self.rules [irule] [:2])

			if not func:
				raise NameError (f"no method for rule '{self.rules [irule] [0]} -> {''' '''.join (self.rules [irule] [1])}'")

			self.rfuncs.append (func)

	def tokenize (self, text):
		tokens = []
		end    = len (text)
		pos    = 0

		while pos < end:
			m = self.tokrec.match (text, pos)

			if m is None:
				tokens.append (Token ('$err', text [pos], pos))

				break

			else:
				if m.lastgroup != 'ignore':
					tok  = m.lastgroup
					s, e = self.tokgrps [tok]
					grps = m.groups () [s : e]

					tokens.append (Token (tok, grps [0], pos, grps [1:]))

				pos += len (m.group (0))

		tokens.append (Token ('$end', '', pos))

		return tokens

	#...............................................................................................
	def parse_getextrastate (self):
		return None

	def parse_setextrastate (self, state):
		pass

	def parse_error (self):
		return False # True if state fixed to continue parsing, False to fail

	def parse_success (self, red):
		'NO PARSE_SUCCESS'
		return None # True to contunue checking conflict backtracks, False to stop and return

	def parse (self, src):
		has_parse_success = (self.parse_success.__doc__ != 'NO PARSE_SUCCESS')

		rules, terms, nterms, rfuncs = self.rules, self.terms, self.nterms, self.rfuncs

		tokens = self.tokenize (src)
		tokidx = 0
		cstack = [] # [(action, tokidx, stack, stidx, extra state), ...] # conflict backtrack stack
		stack  = [State (0, None, None)] # [(stidx, symbol, reduction) or (stidx, token), ...]
		stidx  = 0
		rederr = None # reduction function raised exception (SyntaxError or Incomplete)

		while 1:
			if not rederr:
				tok       = tokens [tokidx]
				act, conf = terms [stidx].get (tok, (None, None))

			if rederr or act is None:
				self.tokens, self.tokidx, self.cstack, self.stack, self.stidx, self.tok, self.rederr = \
						tokens, tokidx, cstack, stack, stidx, tok, rederr

				rederr = None

				if tok == '$end' and stidx == 1 and len (stack) == 2 and stack [1] [1] == rules [0] [1]:
					if not has_parse_success:
						return stack [1].red

					if not self.parse_success (stack [1].red) or not cstack:
						return None

				elif self.parse_error ():
					tokidx, stidx = self.tokidx, self.stidx

					continue

				elif not cstack:
					if has_parse_success: # do not raise SyntaxError if parser relies on parse_success
						return None

					# if self.rederr is not None: # THIS IS COMMENTED OUT BECAUSE IS NOT USED HERE AND PYLINT DOESN'T LIKE IT!
					# 	raise self.rederr # re-raise exception from last reduction function if present

					raise SyntaxError ( \
						'unexpected end of input' if tok == '$end' else \
						f'invalid token {tok.text!r}' if tok == '$err' else \
						f'invalid syntax {src [tok.pos : tok.pos + 16]!r}')

				act, tokens, tokidx, stack, stidx, estate = cstack.pop ()
				tok                                       = tokens [tokidx]

				self.parse_setextrastate (estate)

			elif conf is not None:
				cstack.append ((conf, tokens [:], tokidx, stack [:], stidx, self.parse_getextrastate ()))

			if act > 0:
				tokidx += 1
				stidx   = act

				stack.append (State (stidx, tok))

			else:
				rule  = rules [-act]
				rnlen = -len (rule [1])
				prod  = rule [0]

				try:
					red = rfuncs [-act] (*((t [-1] for t in stack [rnlen:]) if rnlen else ()))

				except SyntaxError as e:
					rederr = e or True # why did I do this?

					continue

				except Incomplete as e:
					rederr = e
					red    = e.red

				if rnlen:
					del stack [rnlen:]

				stidx = nterms [stack [-1].idx] [prod]

				stack.append (State (stidx, prod, red))

class lalr1: # for single script
	Incomplete = Incomplete
	Token      = Token
	State      = State
	Parser     = Parser
# Base classes for abstract math syntax tree, tuple based.
#
# ('=', 'rel', lhs, rhs)             - equality of type 'rel' relating Left-Hand-Side and Right-Hand-Side
# ('#', 'num')                       - real numbers represented as strings to pass on maximum precision to sympy
# ('@', 'var')                       - variable name, can take forms: 'x', "x'", 'dx', '\partial x', 'something'
# ('.', expr, 'name')                - data member reference
# ('.', expr, 'name', (a1, a2, ...)) - method member call
# ('"', 'str')                       - string
# (',', (expr1, expr2, ...))         - comma expression (tuple)
# ('{', expr)                        - invilible parentheses for grouping
# ('(', expr)                        - explicit parentheses (not tuple)
# ('[', (expr1, expr2, ...))         - brackets (list, not index)
# ('|', expr)                        - absolute value
# ('-', expr)                        - negative of expression, negative numbers are represented with this at least initially
# ('!', expr)                        - factorial
# ('+', (expr1, expr2, ...))         - addition
# ('*', (expr1, expr2, ...))         - multiplication
# ('/', numer, denom)                - fraction numer(ator) / denom(inator)
# ('^', base, exp)                   - power base ^ exp(onent)
# ('log', expr)                      - natural logarithm of expr
# ('log', expr, base)                - logarithm of expr in base
# ('sqrt', expr)                     - square root of expr
# ('sqrt', expr, n)                  - nth root of expr
# ('func', 'func', (a1, a2, ...))    - sympy or regular python function 'func', will be called with sympy expression
# ('lim', expr, var, to)             - limit of expr when variable var approaches to from both positive and negative directions
# ('lim', expr, var, to, 'dir')      - limit of expr when variable var approaches to from specified direction dir which may be '+' or '-'
# ('sum', expr, var, from, to)       - summation of expr over variable var from from to to
# ('diff', expr, (var1, ...))        - differentiation of expr with respect to var1 and optional other vars
# ('intg', expr, var)                - anti-derivative of expr (or 1 if expr is None) with respect to differential var ('dx', 'dy', etc ...)
# ('intg', expr, var, from, to)      - definite integral of expr (or 1 if expr is None) with respect to differential var ('dx', 'dy', etc ...)
# ('vec', (e1, e2, ...))             - vector
# ('mat', ((e11, e12, ...), (e21, e22, ...), ...)) - matrix
# ('piece', ((v1, c1), ..., (vn, True?)))          - piecewise expression: v = AST, c = condition AST, last condition may be True to catch all other cases
# ('lamb', expr, (v1, v2, ...))      - lambda expression: v? = ('@', 'var')
# ('idx', expr, (i0, i1, ...))       - indexing: expr [i0, i1, ...]

import re
import types

import sympy as sp

_SYMPY_OBJECTS = dict ((name, obj) for name, obj in filter (lambda no: no [0] [0] != '_', sp.__dict__.items ()))
_SYMPY_FUNCS   = set (no [0] for no in filter (lambda no: len (no [0]) > 1 and callable (no [1]), _SYMPY_OBJECTS.items ()))

#...............................................................................................
class AST (tuple):
	op     = None
	CONSTS = set () # will be filled in after all classes defined

	_rec_identifier = re.compile (r'^[a-zA-Z_]\w*$')

	def __new__ (cls, *args):
		op       = _AST_CLS2OP.get (cls)
		cls_args = tuple (AST (*arg) if arg.__class__ is tuple else arg for arg in args)

		if op:
			args = (op,) + cls_args

		elif args:
			args = cls_args
			cls2 = _AST_OP2CLS.get (args [0])

			if cls2:
				cls      = cls2
				cls_args = cls_args [1:]

		self = tuple.__new__ (cls, args)

		if self.op:
			self._init (*cls_args)

		return self

	def __getattr__ (self, name): # calculate value for nonexistent self.name by calling self._name () and store
		func                 = getattr (self, f'_{name}') if name [0] != '_' else None
		val                  = func and func ()
		self.__dict__ [name] = val

		return val

	def _is_single_unit (self): # is single positive digit, fraction or single non-differential non-subscripted non-primed variable?
		if self.op == '/':
			return True
		elif self.op == '#':
			return len (self.num) == 1
		else:
			return self.is_single_var

	def _len (self):
		return len (self)

	def neg (self, stack = False): # stack means stack negatives ('-', ('-', ('#', '-1')))
		if stack:
			return \
					AST ('-', self)            if not self.is_pos_num else \
					AST ('#', f'-{self.num}')
		else:
			return \
					self.minus                 if self.is_minus else \
					AST ('-', self)            if not self.is_num else \
					AST ('#', self.num [1:])   if self.num [0] == '-' else \
					AST ('#', f'-{self.num}')

	def strip_curlys (self, count = None):
		count = 999999999 if count is None else count

		while self.op == '{' and count:
			self   = self.curly
			count -= 1

		return self

	def remove_curlys (self):
		return \
				self.curly.remove_curlys () \
				if self.is_curly else \
				AST (*tuple (a.remove_curlys () if isinstance (a, AST) else a for a in self))

	def strip_paren (self, count = None):
		count = 999999999 if count is None else count

		while self.op == '(' and count:
			self   = self.paren
			count -= 1

		return self

	def strip_paren_noncomma (self, count = None):
		new = self.strip_paren (count)

		return new if not new.is_comma or not self.is_paren else AST ('(', new)

	def strip (self, count = None):
		count = 999999999 if count is None else count

		while self.op in {'{', '('} and count:
			self   = self [1]
			count -= 1

		return self

	def strip_minus (self, count = None, retneg = False):
		count       = 999999999 if count is None else count
		neg         = lambda ast: ast
		neg.has_neg = False

		while self.op == '-' and count:
			self         = self.minus
			count       -= 1
			neg          = lambda ast, neg = neg: neg (ast.neg (stack = True))
			neg.has_neg  = True

		return (self, neg) if retneg else self

	def strip_mls (self, count = None):
		count = 999999999 if count is None else count

		while self.op in {'*', 'lim', 'sum'} and count:
			self   = self.muls [-1] if self.is_mul else self [1]
			count -= 1

		return self

	def as_identifier (self, top = True):
		if self.op in {'#', '@', '"'}:
			name = self [1]
		elif not self.is_mul:
			return None

		else:
			try:
				name = ''.join (m.as_identifier () for m in self.muls)
			except TypeError:
				return None

		return name if AST._rec_identifier.match (name) else None

	@staticmethod
	def _free_vars (ast, vars):
		if isinstance (ast, AST):
			if ast.is_const_var is False and ast.var:
				vars.add (ast)

			for e in ast:
				AST._free_vars (e, vars)

	def free_vars (self): # return set of unique unbound variables found in tree
		vars = set ()

		AST._free_vars (self, vars)

		return vars

	@staticmethod
	def is_int_text (text):
		return AST_Num._rec_int.match (text)

	@staticmethod
	def flatcat (op, ast0, ast1): # ,,,/O.o\,,,~~
		if ast0.op == op:
			return \
					AST (op, ast0 [-1] + ast1 [-1]) \
					if ast1.op == op else \
					AST (op, ast0 [-1] + (ast1,))

		else: # ast0.op != op
			return \
					AST (op, (ast0,) + ast1 [-1]) \
					if ast1.op == op else \
					AST (op, (ast0, ast1))

#...............................................................................................
class AST_Eq (AST):
	op, is_eq  = '=', True

	TEX2PY = {'\\ne': '!=', '\\le': '<=', '\\ge': '>=', '\\lt': '<', '\\gt': '>', '\\neq': '!='}
	UNI2PY = {'\u2260': '!=', '\u2264': '<=', '\u2265': '>='}
	ANY2PY = {**UNI2PY, **TEX2PY}
	PY2TEX = {'!=': '\\ne', '<=': '\\le', '>=': '\\ge'} # , '<': '\\lt', '>': '\\gt'}

	def _init (self, rel, lhs, rhs):
		self.rel, self.lhs, self.rhs = rel, lhs, rhs # should be short form

	_is_ass = lambda self: self.rel == '='

class AST_Num (AST):
	op, is_num = '#', True

	_rec_int          = re.compile (r'^-?\d+$')
	_rec_pos_int      = re.compile (r'^\d+$')
	_rec_mant_and_exp = re.compile (r'^(-?\d*\.?\d*)[eE](?:(-\d+)|\+?(\d+))$')

	def _init (self, num):
		self.num = num

	_is_pos_num = lambda self: self.num [0] != '-'
	_is_neg_num = lambda self: self.num [0] == '-'
	_is_pos_int = lambda self: AST_Num._rec_pos_int.match (self.num)

	def _mant_and_exp (self):
		m = AST_Num._rec_mant_and_exp.match (self.num)

		return (self.num, None) if not m else (m.group (1) , m.group (2) or m.group (3))

class AST_Var (AST):
	op, is_var = '@', True

	GREEK       = {'alpha', 'beta', 'gamma', 'delta', 'epsilon', 'zeta', 'eta', 'theta', 'iota', 'kappa', 'lambda', 'mu', 'nu', 'xi', 'pi', 'rho', 'sigma', \
			'tau', 'upsilon', 'phi', 'chi', 'psi', 'omega', 'Gamma', 'Delta', 'Theta', 'Lambda', 'Xi', 'Pi', 'Sigma', 'Upsilon', 'Phi', 'Psi', 'Omega'}
	GREEKUNI    = {'\u03b1', '\u03b2', '\u03b3', '\u03b4', '\u03b5', '\u03b6', '\u03b7', '\u03b8', '\u03b9', '\u03ba', '\u03bb', '\u03bc', '\u03bd', '\u03be', '\u03c0', '\u03c1', '\u03c3', \
			'\u03c4', '\u03c5', '\u03c6', '\u03c7', '\u03c8', '\u03c9', '\u0393', '\u0394', '\u0398', '\u0398', '\u039e', '\u03a0', '\u03a3', '\u03a5', '\u03a6', '\u03a8', '\u03a9'}

	TEX2PY      = {**dict ((f'\\{g}', g) for g in GREEK), '\\partial': 'partial', '\\infty': 'oo', \
			'\\overline\\infty': 'zoo', '\\bar\\infty': 'zoo', '\\widetilde\\infty': 'zoo', '\\tilde\\infty': 'zoo'}
	UNI2PY      = {**dict (zip (GREEKUNI, GREEK)), '\u2202': 'partial', '\u221e': 'oo'}
	ANY2PY      = {**UNI2PY, **TEX2PY}
	PY2TEX      = {**dict ((g, f'\\{g}') for g in GREEK), 'partial': '\\partial', 'oo': '\\infty', 'zoo': '\\widetilde\\infty'}

	_rec_groups = re.compile (r"^(?:(?:(d(?!elta|partial))|(partial))(?!['\d]))?(.*)$")

	def _init (self, var):
		self.var = var

		if AST._rec_identifier.match (var):
			self.__dict__ [f'is_var_{var}'] = True

	_grp                  = lambda self: AST_Var._rec_groups.match (self.var).groups ()
	_is_null_var          = lambda self: not self.var
	_is_long_var          = lambda self: len (self.var) > 1 and self.var not in AST_Var.PY2TEX
	_is_const_var         = lambda self: self.var in AST.CONSTS
	_is_nonconst_var      = lambda self: self.var not in AST.CONSTS
	_is_differential      = lambda self: self.grp [0] and self.grp [2]
	_is_diff_solo         = lambda self: self.grp [0] and not self.grp [2]
	_is_diff_any          = lambda self: self.grp [0]
	_is_partial           = lambda self: self.grp [1] and self.grp [2]
	_is_part_solo         = lambda self: self.grp [1] and not self.grp [2]
	_is_part_any          = lambda self: self.grp [1]
	_is_diff_or_part      = lambda self: (self.grp [0] or self.grp [1]) and self.grp [2]
	_is_diff_or_part_solo = lambda self: (self.grp [0] or self.grp [1]) and not self.grp [2]
	_diff_or_part_type    = lambda self: self.grp [0] or self.grp [1] or '' # 'dx' -> 'd', 'partialx' -> 'partial', else ''
	_is_single_var        = lambda self: len (self.var) == 1 or self.var in AST_Var.PY2TEX # is single atomic variable (non-differential, non-subscripted, non-primed)?
	_as_var               = lambda self: AST ('@', self.grp [2]) if self.var else self # 'x', dx', 'partialx' -> 'x'
	_as_diff              = lambda self: AST ('@', f'd{self.grp [2]}') if self.var else self # 'x', 'dx', 'partialx' -> 'dx'

class AST_Attr (AST):
	op, is_attr = '.', True

	def _init (self, obj, attr, args = None):
		self.obj, self.attr, self.args = obj, attr, args

class AST_Str (AST):
	op, is_str = '"', True

	def _init (self, str_):
		self.str_ = str_

class AST_Comma (AST):
	op, is_comma = ',', True

	def _init (self, commas):
		self.commas = commas

	# _len = lambda self: len (self.commas)

class AST_Curly (AST):
	op, is_curly = '{', True

	def _init (self, curly):
		self.curly = curly

	# _len = lambda self: len (self.paren)

class AST_Paren (AST):
	op, is_paren = '(', True

	def _init (self, paren):
		self.paren = paren

	# _len = lambda self: len (self.paren)

class AST_Brack (AST):
	op, is_brack = '[', True

	def _init (self, brack):
		self.brack = brack

	# _len = lambda self: len (self.brack)

class AST_Abs (AST):
	op, is_abs = '|', True

	def _init (self, abs):
		self.abs = abs

class AST_Minus (AST):
	op, is_minus = '-', True

	def _init (self, minus):
		self.minus = minus

class AST_Fact (AST):
	op, is_fact = '!', True

	def _init (self, fact):
		self.fact = fact

class AST_Add (AST):
	op, is_add = '+', True

	def _init (self, adds):
		self.adds = adds

	# _len = lambda self: len (self.adds)

class AST_Mul (AST):
	op, is_mul = '*', True

	def _init (self, muls):
		self.muls = muls

	def _is_mul_has_abs (self):
		for m in self.muls:
			if m.is_abs:
				return True

	# _len = lambda self: len (self.muls)

class AST_Div (AST):
	op, is_div = '/', True

	def _init (self, numer, denom):
		self.numer, self.denom = numer, denom

class AST_Pow (AST):
	op, is_pow = '^', True

	def _init (self, base, exp):
		self.base, self.exp = base, exp

class AST_Log (AST):
	op, is_log = 'log', True

	def _init (self, log, base = None):
		self.log, self.base = log, base

class AST_Sqrt (AST):
	op, is_sqrt = 'sqrt', True

	def _init (self, rad, idx = None):
		self.rad, self.idx = rad, idx

class AST_Func (AST):
	op, is_func = 'func', True

	ESCAPE          = '$'
	NOREMAP         = '@'
	NOEVAL          = '%'

	ADMIN           = {'vars', 'funcs', 'del', 'delvars', 'delall', 'sympyEI', 'quick'}
	SPECIAL         = ADMIN | {NOREMAP, NOEVAL}
	BUILTINS        = {'max', 'min', 'abs', 'pow', 'str', 'sum', 'print'}
	TEXNATIVE       = {'max', 'min', 'arg', 'deg', 'exp', 'gcd'}
	TRIGH           = {'sin', 'cos', 'tan', 'cot', 'sec', 'csc', 'sinh', 'cosh', 'tanh', 'coth', 'sech', 'csch'}

	PY_TRIGHINV     = {f'a{f}' for f in TRIGH}
	TEX_TRIGHINV    = {f'arc{f}' for f in TRIGH}
	TEX2PY_TRIGHINV = {f'arc{f}': f'a{f}' for f in TRIGH}

	PY              = SPECIAL | BUILTINS | PY_TRIGHINV | TRIGH | _SYMPY_FUNCS - {'sqrt', 'log', 'ln', 'evaluate', 'beta', 'gamma', 'zeta', 'Lambda'}
	TEX             = TEXNATIVE | TEX_TRIGHINV | (TRIGH - {'sech', 'csch'})

	_rec_trigh        = re.compile (r'^a?(?:sin|cos|tan|csc|sec|cot)h?$')
	_rec_trigh_inv    = re.compile (r'^a(?:sin|cos|tan|csc|sec|cot)h?$')
	_rec_trigh_noninv = re.compile (r'^(?:sin|cos|tan|csc|sec|cot)h?$')

	def _init (self, func, args):
		self.func, self.args = func, args

		if AST._rec_identifier.match (func):
			self.__dict__ [f'is_func_{func}'] = True

	_is_trigh_func        = lambda self: AST_Func._rec_trigh.match (self.func)
	_is_trigh_func_inv    = lambda self: AST_Func._rec_trigh_inv.match (self.func)
	_is_trigh_func_noninv = lambda self: AST_Func._rec_trigh_noninv.match (self.func)
	_is_escaped           = lambda self: self.func [:1] == self.ESCAPE
	_unescaped            = lambda self: self.func.lstrip (self.ESCAPE)

class AST_Lim (AST):
	op, is_lim = 'lim', True

	def _init (self, lim, lvar, to, dir = None):
		self.lim, self.lvar, self.to, self.dir = lim, lvar, to, dir

class AST_Sum (AST):
	op, is_sum = 'sum', True

	def _init (self, sum, svar, from_, to):
		self.sum, self.svar, self.from_, self.to = sum, svar, from_, to

class AST_Diff (AST):
	op, is_diff = 'diff', True

	def _init (self, diff, dvs):
		self.diff, self.dvs = diff, dvs

	_diff_type = lambda self: '' if not self.dvs else self.dvs [0].diff_or_part_type if self.dvs [0].is_var else self.dvs [0].base.diff_or_part_type

class AST_Intg (AST):
	op, is_intg = 'intg', True

	def _init (self, intg, dv, from_ = None, to = None):
		self.intg, self.dv, self.from_, self.to = intg, dv, from_, to

class AST_Vec (AST):
	op, is_vec = 'vec', True

	def _init (self, vec):
		self.vec = vec

class AST_Mat (AST):
	op, is_mat = 'mat', True

	def _init (self, mat):
		self.mat = mat

	_rows = lambda self: len (self.mat)
	_cols = lambda self: len (self.mat [0]) if self.mat else 0

class AST_Piece (AST):
	op, is_piece = 'piece', True

	def _init (self, pieces):
		self.pieces = pieces

class AST_Lamb (AST):
	op, is_lamb = 'lamb', True

	def _init (self, lamb, vars):
		self.lamb, self.vars = lamb, vars

class AST_Idx (AST):
	op, is_idx = 'idx', True

	def _init (self, obj, idx):
		self.obj, self.idx = obj, idx

#...............................................................................................
_AST_OP2CLS = {
	'=': AST_Eq,
	'#': AST_Num,
	'@': AST_Var,
	'.': AST_Attr,
	'"': AST_Str,
	',': AST_Comma,
	'{': AST_Curly,
	'(': AST_Paren,
	'[': AST_Brack,
	'|': AST_Abs,
	'-': AST_Minus,
	'!': AST_Fact,
	'+': AST_Add,
	'*': AST_Mul,
	'/': AST_Div,
	'^': AST_Pow,
	'log': AST_Log,
	'sqrt': AST_Sqrt,
	'func': AST_Func,
	'lim': AST_Lim,
	'sum': AST_Sum,
	'diff': AST_Diff,
	'intg': AST_Intg,
	'vec': AST_Vec,
	'mat': AST_Mat,
	'piece': AST_Piece,
	'lamb': AST_Lamb, # not to be confused with the Greek variable lambda
	'idx': AST_Idx,
}

_AST_CLS2OP = dict ((b, a) for (a, b) in _AST_OP2CLS.items ())

for cls in _AST_CLS2OP:
	setattr (AST, cls.__name__ [4:], cls)

AST.OPS      = set (_AST_OP2CLS)
AST.Zero     = AST ('#', '0')
AST.One      = AST ('#', '1')
AST.NegOne   = AST ('#', '-1')
AST.VarNull  = AST ('@', '')
AST.MatEmpty = AST ('func', 'Matrix', ('[', ()))

_CONSTS      = (('E', 'e'), ('I', 'i'), ('Pi', 'pi'), ('Infty', 'oo'), ('CInfty', 'zoo'), ('None_', 'None'), ('True_', 'True'), ('False_', 'False'), ('NaN', 'nan'),
		('Naturals', 'Naturals'), ('Naturals0', 'Naturals0'), ('Integers', 'Integers'), ('Reals', 'Reals'), ('Complexes', 'Complexes'))

for _vp, _vv in _CONSTS:
	ast = AST ('@', _vv)

	AST.CONSTS.add (ast)
	setattr (AST, _vp, ast)

def register_AST (cls):
	_AST_OP2CLS [cls.op] = cls
	_AST_CLS2OP [cls]    = cls.op

	AST.OPS.add (cls.op)

	setattr (AST, cls.__name__ [4:], cls)

def sympyEI (yes = True):
	AST.CONSTS.difference_update ((AST.E, AST.I))

	AST.E, AST.I = (AST ('@', 'E'), AST ('@', 'I')) if yes else (AST ('@', 'e'), AST ('@', 'i'))

	AST.CONSTS.update ((AST.E, AST.I))

class sast: # for single script
	AST          = AST
	register_AST = register_AST
	sympyEI      = sympyEI

# if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: ## DEBUG!
# 	ast = AST ('func', 'exp', AST (('@', 'x'),))
# 	print (ast)
# Translate SymPy functions to other ASTs for display.


def _xlat_func_Derivative (ast = AST.VarNull, *dvs):
	ds = []

	if not dvs:
		vars = ast.free_vars ()

		if len (vars) == 1:
			ds = [AST ('@', f'd{vars.pop ().var}')]

	else:
		dvs = list (dvs [::-1])

		while dvs:
			v = dvs.pop ()

			if not v.is_var:
				return None
			elif dvs and dvs [-1].is_pos_int:
				ds.append (AST ('^', ('@', f'd{v.var}'), dvs.pop ()))
			else:
				ds.append (AST ('@', f'd{v.var}'))

	return AST ('diff', ast, tuple (ds))

def _xlat_func_Integral (ast = None, dvab = None, *args):
	if ast is None:
		return AST ('intg', AST.VarNull, AST.VarNull)

	if dvab is None:
		vars = ast.free_vars ()

		if len (vars) == 1:
			return AST ('intg', ast, ('@', f'd{vars.pop ().var}'))

		return AST ('intg', AST.VarNull, AST.VarNull)

	dvab = dvab.strip_paren ()
	ast2 = None

	if dvab.is_comma:
		if dvab.commas and dvab.commas [0].is_nonconst_var:
			if dvab.commas.len == 1:
				ast2 = AST ('intg', ast, ('@', f'd{dvab.commas [0].var}'))
			elif dvab.commas.len == 2:
				ast2 = AST ('intg', ast, ('@', f'd{dvab.commas [0].var}'), AST.Zero, dvab.commas [1])
			elif dvab.commas.len == 3:
				ast2 = AST ('intg', ast, ('@', f'd{dvab.commas [0].var}'), dvab.commas [1], dvab.commas [2])

	elif dvab.is_var:
		ast2 = AST ('intg', ast, ('@', f'd{dvab.var}'))

	if ast2 is None:
		return None

	return _xlat_func_Integral (ast2, *args) if args else ast2

_xlat_func_Limit_dirs = {AST ('"', '+'): ('+',), AST ('"', '-'): ('-',), AST ('"', '+-'): ()}

def _xlat_func_Limit (ast = AST.VarNull, var = AST.VarNull, to = AST.VarNull, dir = AST ('"', '+')):
	return AST ('lim', ast, var, to, *_xlat_func_Limit_dirs [dir])

def _xlat_func_Pow (ast = AST.VarNull, exp = AST.VarNull):
	return AST ('^', ast, exp)

def _xlat_func_Matrix (ast = AST.VarNull):
	if ast == AST.VarNull:
		return AST ('vec', ())

	if ast.is_brack and ast.brack:
		if not ast.brack [0].is_brack: # single layer or brackets, column matrix?
			return AST ('vec', ast.brack)

		elif ast.brack [0].brack:
			rows = [ast.brack [0].brack]
			cols = len (rows [0])

			for row in ast.brack [1 : -1]:
				if len (row.brack) != cols:
					break

				rows.append (row.brack)

			else:
				l = len (ast.brack [-1].brack)

				if l <= cols:
					if len (ast.brack) > 1:
						rows.append (ast.brack [-1].brack + (AST.VarNull,) * (cols - l))

					if l != cols:
						return AST ('mat', tuple (rows))

					return \
							AST ('mat', tuple (rows)) \
							if cols > 1 else \
							AST ('vec', tuple (r [0] for r in rows))

	return None

def _xlat_func_Piecewise (*args):
	pcs = []

	if not args or args [0].is_null_var:
		return AST ('piece', ((AST.VarNull, AST.VarNull),))

	if len (args) > 1:
		for c in args [:-1]:
			c = c.strip ()

			if not c.is_comma or len (c.commas) != 2:
				return None

			pcs.append (c.commas)

	ast = args [-1]

	if not ast.is_paren:
		return None

	ast = ast.strip ()
	pcs = tuple (pcs)

	if not ast.is_comma:
		return AST ('piece', pcs + ((ast, AST.VarNull),))
	if len (ast.commas) == 0:
		return AST ('piece', pcs + ())

	if not ast.commas [0].is_comma:
		if len (ast.commas) == 1:
			return AST ('piece', pcs + ((ast.commas [0], AST.VarNull),))
		if len (ast.commas) == 2:
			return AST ('piece', pcs + ((ast.commas [0], True if ast.commas [1] == AST.True_ else ast.commas [1]),))

	return None

def _xlat_func_Sum (ast = AST.VarNull, ab = None):
	if ab is None:
		return AST ('sum', ast, AST.VarNull, AST.VarNull, AST.VarNull)

	ab = ab.strip_paren ()

	if ab.is_var:
		return AST ('sum', ast, ab, AST.VarNull, AST.VarNull)
	if ab.is_comma and ab.commas and ab.commas.len <= 3 and ab.commas [0].is_var:
		return AST ('sum', ast, *ab.commas, *((AST.VarNull,) * (3 - ab.commas.len)))

	return None

XLAT_FUNC_NAT = {
	'abs'                  : lambda ast: AST ('|', ast),
	'Abs'                  : lambda ast: AST ('|', ast),
	'Derivative'           : _xlat_func_Derivative,
	'diff'                 : _xlat_func_Derivative,
	'exp'                  : lambda ast: AST ('^', AST.E, ast),
	'factorial'            : lambda ast: AST ('!', ast),
	'Integral'             : _xlat_func_Integral,
	'integrate'            : _xlat_func_Integral,
	'Limit'                : _xlat_func_Limit,
	'limit'                : _xlat_func_Limit,
	'Matrix'               : _xlat_func_Matrix,
	'Piecewise'            : _xlat_func_Piecewise,
	'Pow'                  : _xlat_func_Pow,
	'pow'                  : _xlat_func_Pow,
	'Sum'                  : _xlat_func_Sum,
}

XLAT_FUNC_TEX = {**XLAT_FUNC_NAT,
	'MutableDenseMatrix'   : _xlat_func_Matrix,
	'MutableSparseMatrix'  : _xlat_func_Matrix,
	'ImmutableDenseMatrix' : _xlat_func_Matrix,
	'ImmutableSparseMatrix': _xlat_func_Matrix,
	'diag'                 : True,
	'eye'                  : True,
	'ones'                 : True,
	'zeros'                : True,
}

def xlat_func (xact, args):
	xargs = []
	xkw   = {}

	for arg in args:
		if arg.is_ass:
			xkw [arg.lhs.as_identifier ()] = arg.rhs
		elif xkw:
			raise SyntaxError ('positional argument follows keyword argument')
		else:
			xargs.append (arg)

	return xact (*xargs, **xkw)

class xlat: # for single script
	XLAT_FUNC_NAT = XLAT_FUNC_NAT
	XLAT_FUNC_TEX = XLAT_FUNC_TEX
	xlat_func     = xlat_func

# if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: ## DEBUG!
# 	ast = AST ('(', (',', (('#', '1'), ('#', '2'))))
# 	res = XLAT_FUNC_NAT ['Piecewise'] (ast)
# 	print (res)
# Convert between internal AST and sympy expressions and write out LaTeX, simple and python code

import re
import sympy as sp

sp.numbers   = sp.numbers # medication for pylint
sp.boolalg   = sp.boolalg
sp.fancysets = sp.fancysets


_SYMPY_FLOAT_PRECISION = None
_USER_FUNCS            = set () # set or dict of user function names

class AST_Text (AST): # for displaying elements we do not know how to handle, only returned from SymPy processing, not passed in
	op = 'text'

	def _init (self, tex, nat = None, py = None, spt = None):
		self.tex, self.nat, self.py, self.spt = tex, (tex if nat is None else nat), (tex if py is None else py), spt

sast.register_AST (AST_Text)

class ExprDontDoIt (sp.Expr): # prevent doit() evaluation of expression a number of times
	def doit (self, *args, **kwargs):
		return self.args [0] if self.args [1] == 1 else ExprDontDoIt (self.args [0], self.args [1] - 1)

def _tuple2ast (args):
	return args [0] if len (args) == 1 else AST (',', args)

def _trail_comma (obj):
	return ',' if len (obj) == 1 else ''

def _ast_is_neg (ast):
	return ast.is_minus or ast.is_neg_num or (ast.is_mul and _ast_is_neg (ast.muls [0]))

def _ast_func_call (func, args, _ast2spt = None, is_escaped = False, **kw):
	if _ast2spt is None:
		_ast2spt = ast2spt

	pyargs = []
	pykw   = {}

	for arg in args:
		if arg.is_ass:
			pykw [arg.lhs.as_identifier ()] = _ast2spt (arg.rhs)
		elif pykw:
			raise SyntaxError ('positional argument follows keyword argument')
		else:
			pyargs.append (_ast2spt (arg))

	try:
		spt = func (*pyargs, **{**kw, **pykw})
	except: # try again if function does not support **kw
		spt = func (*pyargs, **pykw)

	if type (spt) is func and not kw.get ('evaluate', True):
		spt._SYMPAD_ESCAPED = is_escaped

	return spt

def _ast_xlat_funcs (ast, XLAT): # translate eligible functions in tree to other AST representations
	if not isinstance (ast, AST):
		return ast

	if ast.is_func:
		xact = XLAT.get (ast.func)

		if xact is not None:
			args = AST (*(_ast_xlat_funcs (arg, XLAT) for arg in ast.args))

			if xact is True: # True means execute function and use return value for ast
				return spt2ast (_ast_func_call (getattr (sp, ast.func), args))

			try:
				ast2 = xlat.xlat_func (xact, args)

				if ast2 is not None:
					return ast2

			except:
				pass

			return AST ('func', ast.func, args)

	return AST (*(_ast_xlat_funcs (e, XLAT) for e in ast))

#...............................................................................................
def ast2tex (ast, doxlat = True): # abstract syntax tree -> LaTeX text
	return _ast2tex (_ast_xlat_funcs (ast, xlat.XLAT_FUNC_TEX) if doxlat else ast)

def _ast2tex (ast):
	return _ast2tex_funcs [ast.op] (ast)

def _ast2tex_wrap (obj, curly = None, paren = None):
	s = _ast2tex (obj) if isinstance (obj, AST) else str (obj)

	if (obj.op in paren) if isinstance (paren, set) else paren:
		return f'\\left({s} \\right)'

	if (obj.op in curly) if isinstance (curly, set) else curly:
		return f'{{{s}}}'

	return s

def _ast2tex_curly (ast):
	return \
			f'{_ast2tex (ast)}'                     if ast.is_single_unit else \
			f'{{{_ast2tex (ast)}}}'                 if not ast.is_comma else \
			f'{{\\left({_ast2tex (ast)}\\right)}}'

def _ast2tex_paren (ast, ops = {}):
	return _ast2tex_wrap (ast, 0, not (ast.is_paren or (ops and ast.op not in ops)))

def _ast2tex_paren_mul_exp (ast, ret_has = False, also = {'=', '+'}):
	if ast.is_mul:
		s, has = _ast2tex_mul (ast, True)
	else:
		s, has = _ast2tex (ast), ast.op in also

	s = _ast2tex_wrap (s, 0, has)

	return (s, has) if ret_has else s

def _ast2tex_eq_hs (ast, hs, lhs = True):
	return _ast2tex_wrap (hs, 0, (hs.is_ass or (lhs and hs.op in {',', 'piece'})) if ast.is_ass else {'=', 'piece'})

def _ast2tex_num (ast):
	m, e = ast.mant_and_exp

	return m if e is None else f'{m} \\cdot 10^{_ast2tex_curly (AST ("#", e))}'

_ast2tex_var_xlat = {'Naturals', 'Naturals0', 'Integers', 'Reals', 'Complexes'}

def _ast2tex_var (ast):
	if not ast.var:
		return '{}' # Null var

	if ast.var in _ast2tex_var_xlat:
		return sp.latex (getattr (sp, ast.var))

	v = ast.as_var.var
	p = ''

	while v [-6:] == '_prime':
		v, p = v [:-6], p + "'"

	n = v.replace ('_', '\\_')
	t = AST.Var.PY2TEX.get (n)

	return \
			f'{t or n}{p}'       if not ast.diff_or_part_type else \
			f'd{t or n}{p}'		   if ast.is_diff_any else \
			f'\\partial{p}'      if ast.is_part_solo else \
			f'\\partial{t}{p}'   if t else \
			f'\\partial {n}{p}'  if n else \
			f'\\partial{p}'

def _ast2tex_attr (ast):
	a = ast.attr.replace ('_', '\\_')
	a = a if ast.args is None else f'\\operatorname{{{a}}}{_ast2tex_paren (_tuple2ast (ast.args))}'

	return f'{_ast2tex_paren (ast.obj, {"=", "#", ",", "-", "+", "*", "/", "lim", "sum", "intg", "piece"})}.{a}'

def _ast2tex_add (ast):
	return ' + '.join (_ast2tex_wrap (n, \
			((n.strip_mls ().is_intg or (n.is_mul and n.muls [-1].strip_mls ().is_intg)) and n is not ast.adds [-1]), \
			(n.op in ("piece") and n is not ast.adds [-1]) or n.op in {'='})
			for n in ast.adds).replace (' + -', ' - ')

def _ast2tex_mul (ast, ret_has = False):
	t   = []
	p   = None
	has = False

	for n in ast.muls:
		s = _ast2tex_wrap (n, \
				_ast_is_neg (n) or (n.strip_mls ().is_intg and n is not ast.muls [-1]), \
				n.op in {'=', '+'} or (n.is_piece and n is not ast.muls [-1]))

		if p and p.is_attr and s [:6] == '\\left(':
			s = _ast2tex_wrap (s, 1)

		if p and (n.op in {'#', '[', '!', 'mat'} or n.is_null_var or p.op in {'lim', 'sum', 'diff', 'intg', 'mat'} or \
				(n.is_pow and n.base.is_pos_num) or (n.op in {'/', 'diff'} and p.op in {'#', '/'}) or _ast_is_neg (n) or \
				(p.is_div and (p.numer.is_diff_or_part_solo or (p.numer.is_pow and p.numer.base.is_diff_or_part_solo)))):
			t.append (f' \\cdot {s}')
			has = True

		elif p and (p.op in {'sqrt'} or \
				p.is_diff_or_part_solo or n.is_diff_or_part_solo or p.is_diff_or_part or n.is_diff_or_part or \
				(p.is_long_var and n.op not in {'(', '['}) or (n.is_long_var and p.op not in {'(', '['})):
			t.append (f'\\ {s}')

		else:
			t.append (f'{"" if not p else " "}{s}')

		p = n

	return (''.join (t), has) if ret_has else ''.join (t)

def _ast2tex_pow (ast, trighpow = True):
	b = _ast2tex_wrap (ast.base, {'mat'}, not (ast.base.op in {'@', '"', '(', '|', 'func', 'mat'} or ast.base.is_pos_num))
	p = _ast2tex_curly (ast.exp)

	if ast.base.is_trigh_func_noninv and ast.exp.is_single_unit and trighpow:
		i = len (ast.base.func) + (15 if ast.base.func in {'sech', 'csch'} else 1)

		return f'{b [:i]}^{p}{b [i:]}'

	return f'{b}^{p}'

def _ast2tex_log (ast):
	return \
			f'\\ln{_ast2tex_paren (ast.log)}' \
			if ast.base is None else \
			f'\\log_{_ast2tex_curly (ast.base)}{_ast2tex_paren (ast.log)}'

_ast2tex_xlat_func_greek = {
	'beta': '\\beta',
	'gamma': '\\Gamma',
	'Gamma': '\\Gamma',
	'zeta': '\\zeta',
}

def _ast2tex_func (ast):
	if ast.is_trigh_func:
		n = (f'\\operatorname{{{ast.func [1:]}}}^{{-1}}' \
				if ast.func in {'asech', 'acsch'} else \
				f'\\{ast.func [1:]}^{{-1}}') \
				if ast.func [0] == 'a' else \
				(f'\\operatorname{{{ast.func}}}' if ast.func in {'sech', 'csch'} else f'\\{ast.func}')

		return f'{n}\\left({_ast2tex (_tuple2ast (ast.args))} \\right)'

	greek = _ast2tex_xlat_func_greek.get (ast.func)

	return \
			f'{greek}\\left({_ast2tex (_tuple2ast (ast.args))} \\right)' \
			if greek else \
			f'\\{ast.func}\\left({_ast2tex (_tuple2ast (ast.args))} \\right)' \
			if ast.func in AST.Func.TEX else \
			'\\operatorname{' + ast.func.replace ('_', '\\_').replace (AST.Func.NOEVAL, '\\%') + f'}}\\left({_ast2tex (_tuple2ast (ast.args))} \\right)'

def _ast2tex_lim (ast):
	s = _ast2tex (ast.to) if ast.dir is None else (_ast2tex_pow (AST ('^', ast.to, AST.Zero), trighpow = False) [:-1] + ast.dir)

	return f'\\lim_{{{_ast2tex (ast.lvar)} \\to {s}}} {_ast2tex_paren_mul_exp (ast.lim)}'

def _ast2tex_sum (ast):
	return f'\\sum_{{{_ast2tex (ast.svar)} = {_ast2tex (ast.from_)}}}^{_ast2tex_curly (ast.to)} {_ast2tex_paren_mul_exp (ast.sum)}' \

_rec_diff_var_single_start = re.compile (r'^d(?=[^_])')

def _ast2tex_diff (ast):
	ds = set ()
	p  = 0

	for n in ast.dvs:
		if n.is_var:
			p += 1

			if n.var:
				ds.add (n)

		else: # n = ('^', ('@', 'diff or part'), ('#', 'int'))
			p += int (n.exp.num)
			ds.add (n.base)

	if not ds:
		return f'\\frac{{d}}{{}}{_ast2tex_paren (ast.diff)}'

	dv = next (iter (ds))

	if len (ds) == 1 and not dv.is_partial:
		return f'\\frac{{d{"" if p == 1 else f"^{p}"}}}{{{" ".join (_ast2tex (n) for n in ast.dvs)}}}{_ast2tex_paren (ast.diff)}'

	else:
		s = ''.join (_rec_diff_var_single_start.sub (r'\\partial ', _ast2tex (n)) for n in ast.dvs)

		return f'\\frac{{\\partial{"" if p == 1 else f"^{p}"}}}{{{s}}}{_ast2tex_paren (ast.diff)}'

def _ast2tex_intg (ast):
	if ast.from_ is None:
		return \
				f'\\int \\ {_ast2tex (ast.dv)}' \
				if ast.intg is None else \
				f'\\int {_ast2tex_wrap (ast.intg, {"diff"}, {"="})} \\ {_ast2tex (ast.dv)}'
	else:
		return \
				f'\\int_{_ast2tex_curly (ast.from_)}^{_ast2tex_curly (ast.to)} \\ {_ast2tex (ast.dv)}' \
				if ast.intg is None else \
				f'\\int_{_ast2tex_curly (ast.from_)}^{_ast2tex_curly (ast.to)} {_ast2tex_wrap (ast.intg, {"diff"}, {"="})} \\ {_ast2tex (ast.dv)}'

_ast2tex_funcs = {
	'=': lambda ast: f'{_ast2tex_eq_hs (ast, ast.lhs)} {AST.Eq.PY2TEX.get (ast.rel, ast.rel)} {_ast2tex_eq_hs (ast, ast.rhs, False)}',
	'#': _ast2tex_num,
	'@': _ast2tex_var,
	'.': _ast2tex_attr,
	'"': lambda ast: f'\\text{{{repr (ast.str_)}}}',
	',': lambda ast: f'{", ".join (_ast2tex (c) for c in ast.commas)}{_trail_comma (ast.commas)}',
	'(': lambda ast: _ast2tex_wrap (ast.paren, 0, not ast.paren.is_lamb),
	'[': lambda ast: f'\\left[{", ".join (_ast2tex (b) for b in ast.brack)} \\right]',
	'|': lambda ast: f'\\left|{_ast2tex (ast.abs)} \\right|',
	'-': lambda ast: f'-{_ast2tex_wrap (ast.minus, ast.minus.is_pos_num or ast.minus.is_mul, {"=", "+"})}',
	'!': lambda ast: _ast2tex_wrap (ast.fact, {'^'}, (ast.fact.op not in {'#', '@', '"', '(', '|', '!', '^', 'vec', 'mat'} or ast.fact.is_neg_num)) + '!',
	'+': _ast2tex_add,
	'*': _ast2tex_mul,
	'/': lambda ast: f'\\frac{{{_ast2tex_wrap (ast.numer, 0, (ast.numer.base.is_diff_or_part_solo and ast.numer.exp.remove_curlys ().is_pos_int) if ast.numer.is_pow else ast.numer.is_diff_or_part_solo)}}}{{{_ast2tex (ast.denom)}}}',
	'^': _ast2tex_pow,
	'log': _ast2tex_log,
	'sqrt': lambda ast: f'\\sqrt{{{_ast2tex (ast.rad.strip_paren_noncomma (1))}}}' if ast.idx is None else f'\\sqrt[{_ast2tex (ast.idx)}]{{{_ast2tex (ast.rad.strip_paren_noncomma (1))}}}',
	'func': _ast2tex_func,
	'lim': _ast2tex_lim,
	'sum': _ast2tex_sum,
	'diff': _ast2tex_diff,
	'intg': _ast2tex_intg,
	'vec': lambda ast: '\\begin{bmatrix} ' + r' \\ '.join (_ast2tex (e) for e in ast.vec) + ' \\end{bmatrix}',
	'mat': lambda ast: '\\begin{bmatrix} ' + r' \\ '.join (' & '.join (_ast2tex (e) for e in row) for row in ast.mat) + f'{" " if ast.mat else ""}\\end{{bmatrix}}',
	'piece': lambda ast: '\\begin{cases} ' + r' \\ '.join (f'{_ast2tex_wrap (p [0], 0, {"=", ","})} & \\text{{otherwise}}' if p [1] is True else f'{_ast2tex_wrap (p [0], 0, {"=", ","})} & \\text{{for}}\\: {_ast2tex (p [1])}' for p in ast.pieces) + ' \\end{cases}',
	'lamb': lambda ast: f'\\left({_ast2tex (ast.vars [0] if len (ast.vars) == 1 else AST ("(", (",", ast.vars)))} \\mapsto {_ast2tex_wrap (ast.lamb, 0, ast.lamb.is_ass)} \\right)',
	'idx': lambda ast: f'{_ast2tex_wrap (ast.obj, 0, ast.obj.is_neg_num or ast.obj.op in {",", "=", "lamb", "piece", "+", "*", "/", "-", "diff", "intg", "lim", "sum"})}[{_ast2tex (_tuple2ast (ast.idx))}]',

	'text': lambda ast: ast.tex,
}

#...............................................................................................
def ast2nat (ast, doxlat = True): # abstract syntax tree -> simple text
	return _ast2nat (_ast_xlat_funcs (ast, xlat.XLAT_FUNC_NAT) if doxlat else ast)

def _ast2nat (ast):
	return _ast2nat_funcs [ast.op] (ast)

def _ast2nat_wrap (obj, curly = None, paren = None):
	s = _ast2nat (obj) if isinstance (obj, AST) else str (obj)

	if (obj.op in paren) if isinstance (paren, set) else paren:
		return f'({s})'

	if (obj.op in curly) if isinstance (curly, set) else curly:
		return f'{{{s}}}'

	return s

def _ast2nat_curly (ast, ops = {}):
	return _ast2nat_wrap (ast, ops if ops else (ast.is_div or not ast.is_single_unit or (ast.is_var and ast.var in AST.Var.PY2TEX)))

def _ast2nat_paren (ast, ops = {}):
	return _ast2nat_wrap (ast, 0, not (ast.is_paren or (ops and ast.op not in ops)))

def _ast2nat_curly_mul_exp (ast, ret_has = False, also = {}):
	if ast.is_mul:
		s, has = _ast2nat_mul (ast, True)
	else:
		s, has = _ast2nat (ast), False

	has = has or ((ast.op in also) if isinstance (also, set) else also)
	s   = _ast2nat_wrap (s, has)

	return (s, has) if ret_has else s

def _ast2nat_eq_hs (ast, hs, lhs = True):
	return _ast2nat_wrap (hs, 0, (hs.is_ass or (lhs and hs.op in {',', 'piece', 'lamb'})) if ast.is_ass else {'=', 'piece', 'lamb'})

def _ast2nat_add (ast):
	return ' + '.join (_ast2nat_wrap (n, \
			n.is_piece or ((n.strip_mls ().is_intg or (n.is_mul and n.muls [-1].strip_mls ().is_intg)) and n is not ast.adds [-1]), \
			(n.op in ('piece', 'lamb') and n is not ast.adds [-1]) or n.op in {'=', 'lamb'} \
			) for n in ast.adds).replace (' + -', ' - ')

def _ast2nat_mul (ast, ret_has = False):
	t   = []
	p   = None
	has = False

	for n in ast.muls:
		s = _ast2nat_wrap (n, \
				_ast_is_neg (n) or n.is_piece or (n.strip_mls ().is_intg and n is not ast.muls [-1]), \
				n.op in {'=', '+', 'lamb'} or (n.is_piece and n is not ast.muls [-1]))

		if p and (n.op in {'#', '[', '!', 'lim', 'sum', 'intg'} or n.is_null_var or p.op in {'lim', 'sum', 'diff', 'intg'} or \
				(n.is_pow and n.base.is_pos_num) or \
				n.op in {'/', 'diff'} or p.strip_minus ().op in {'/', 'diff'}):
			t.append (f' * {s}')
			has = True

		elif p and (p.is_diff_or_part_solo or \
				(n.op not in {'#', '(', '|', '^'} or p.op not in {'#', '(', '|'})):
			t.append (f' {s}')

		else:
			t.append (s)

		p = n

	return (''.join (t), has) if ret_has else ''.join (t)

def _ast2nat_div (ast):
	n, ns = (_ast2nat_wrap (ast.numer, 1), True) if _ast_is_neg (ast.numer) else \
		(_ast2nat_wrap (ast.numer, 0, 1), True) if ((ast.numer.base.is_diff_or_part_solo and ast.numer.exp.remove_curlys ().is_pos_int) if ast.numer.is_pow else ast.numer.is_diff_or_part_solo) else \
		_ast2nat_curly_mul_exp (ast.numer, True, {'=', '+', '/', 'lim', 'sum', 'diff', 'intg', 'piece', 'lamb'})

	d, ds = (_ast2nat_wrap (ast.denom, 1), True) if _ast_is_neg (ast.denom) else _ast2nat_curly_mul_exp (ast.denom, True, {'=', '+', '/', 'lim', 'sum', 'diff', 'intg', 'piece', 'lamb'})
	s     = ns or ds or ast.numer.strip_minus ().op not in {'#', '@', '*'} or ast.denom.strip_minus ().op not in {'#', '@', '*'}

	return f'{n}{" / " if s else "/"}{d}'

def _ast2nat_pow (ast, trighpow = True):
	b = _ast2nat_wrap (ast.base, 0, not (ast.base.op in {'@', '"', '(', '|', 'mat'} or ast.base.is_pos_num))
	p = _ast2nat_wrap (ast.exp, ast.exp.strip_minus ().op in {'=', '+', '*', '/', 'lim', 'sum', 'diff', 'intg', 'piece', 'lamb'}, {","})

	if ast.base.is_trigh_func_noninv and ast.exp.is_single_unit and trighpow:
		i = len (ast.base.func)

		return f'{b [1 : i + 1]}**{p}{b [i + 1 : -1]}'

	return f'{b}**{p}'

def _ast2nat_log (ast):
	return \
			f'ln{_ast2nat_paren (ast.log)}' \
			if ast.base is None else \
			f'\\log_{_ast2nat_curly (ast.base)}{_ast2nat_paren (ast.log)}'

def _ast2nat_lim (ast):
	s = _ast2nat_wrap (ast.to, {'piece'}) if ast.dir is None else (_ast2nat_pow (AST ('^', ast.to, AST.Zero), trighpow = False) [:-1] + ast.dir)

	return f'\\lim_{{{_ast2nat (ast.lvar)} \\to {s}}} {_ast2nat_curly_mul_exp (ast.lim, False, ast.lim.op in {"=", "+", "piece", "lamb"} or ast.lim.is_mul_has_abs)}'

def _ast2nat_sum (ast):
	return f'\\sum_{{{_ast2nat (ast.svar)}={_ast2nat_curly (ast.from_, {"piece"})}}}^{_ast2nat_curly (ast.to)} {_ast2nat_curly_mul_exp (ast.sum, False, ast.sum.op in {"=", "+", "piece", "lamb"} or ast.sum.is_mul_has_abs)}' \

def _ast2nat_diff (ast):
	p = 0
	d = ''

	for n in ast.dvs:
		if n.is_var:
			d  = n.diff_or_part_type
			p += 1
		else: # n = ('^', ('@', 'differential'), ('#', 'int'))
			d  = n.base.diff_or_part_type
			p += int (n.exp.num)

	return f'{d.strip () if d else "d"}{"" if p == 1 else f"^{p}"} / {" ".join (_ast2nat (n) for n in ast.dvs)} {_ast2nat_paren (ast.diff)}'

def _ast2nat_intg (ast):
	if ast.from_ is None:
		return \
				f'\\int {_ast2nat (ast.dv)}' \
				if ast.intg is None else \
				f'\\int {_ast2nat_wrap (ast.intg, ast.intg.op in {"diff", "piece"} or ast.intg.is_mul_has_abs, {"=", "lamb"})} {_ast2nat (ast.dv)}'
	else:
		return \
				f'\\int_{_ast2nat_curly (ast.from_)}^{_ast2nat_curly (ast.to)} {_ast2nat (ast.dv)}' \
				if ast.intg is None else \
				f'\\int_{_ast2nat_curly (ast.from_)}^{_ast2nat_curly (ast.to)} {_ast2nat_wrap (ast.intg, ast.intg.op in {"diff", "piece"} or ast.intg.is_mul_has_abs, {"=", "lamb"})} {_ast2nat (ast.dv)}'

_ast2nat_funcs = {
	'=': lambda ast: f'{_ast2nat_eq_hs (ast, ast.lhs)} {AST.Eq.PY2TEX.get (ast.rel, ast.rel)} {_ast2nat_eq_hs (ast, ast.rhs, False)}',
	'#': lambda ast: ast.num,
	'@': lambda ast: ast.var,
	'.': lambda ast: f'{_ast2nat_paren (ast.obj, {"=", "#", ",", "-", "+", "*", "/", "lim", "sum", "intg", "piece", "lamb"})}.{ast.attr}' \
			if ast.args is None else f'{_ast2nat (ast.obj)}.{ast.attr}{_ast2nat_paren (_tuple2ast (ast.args))}',
	'"': lambda ast: repr (ast.str_),
	',': lambda ast: f'{", ".join (_ast2nat (c) for c in ast.commas)}{_trail_comma (ast.commas)}',
	'(': lambda ast: f'({_ast2nat (ast.paren)})',
	'[': lambda ast: f'[{", ".join (_ast2nat (b) for b in ast.brack)}]',
	'|': lambda ast: f'{{|{_ast2nat (ast.abs)}|}}',
	'-': lambda ast: f'-{_ast2nat_wrap (ast.minus, ast.minus.is_pos_num or ast.minus.op in {"*", "piece"}, {"=", "+", "lamb"})}',
	'!': lambda ast: _ast2nat_wrap (ast.fact, {'^'}, ast.fact.op not in {'#', '@', '"', '(', '|', '!', '^', 'vec', 'mat'} or ast.fact.is_neg_num) + '!',
	'+': _ast2nat_add,
	'*': _ast2nat_mul,
	'/': _ast2nat_div,
	'^': _ast2nat_pow,
	'log': _ast2nat_log,
	'sqrt': lambda ast: f'sqrt{_ast2nat_paren (ast.rad)}' if ast.idx is None else f'\\sqrt[{_ast2nat (ast.idx)}]{{{_ast2nat (ast.rad.strip_paren_noncomma (1))}}}',
	'func': lambda ast: f'{ast.func}({_ast2nat (_tuple2ast (ast.args))})',
	'lim': _ast2nat_lim,
	'sum': _ast2nat_sum,
	'diff': _ast2nat_diff,
	'intg': _ast2nat_intg,
	'vec': lambda ast: f'{{{", ".join (_ast2nat (e) for e in ast.vec)}{_trail_comma (ast.vec)}}}',
	'mat': lambda ast: ('{' + ', '.join (f'{{{", ".join (_ast2nat (e) for e in row)}{_trail_comma (row)}}}' for row in ast.mat) + f'{_trail_comma (ast.mat)}}}') if ast.mat else 'Matrix([])',
	'piece': lambda ast: ' else '.join (f'{_ast2nat_wrap (p [0], p [0].is_ass or p [0].op in {"piece", "lamb"}, {","})}' if p [1] is True else \
			f'{_ast2nat_wrap (p [0], p [0].is_ass or p [0].op in {"piece", "lamb"}, {","})} if {_ast2nat_wrap (p [1], p [1].is_ass or p [1].op in {"piece", "lamb"}, {","})}' for p in ast.pieces),
	'lamb': lambda ast: f'lambda{" " + ", ".join (v.var for v in ast.vars) if ast.vars else ""}: {_ast2nat_wrap (ast.lamb, 0, ast.lamb.is_eq)}',
	'idx': lambda ast: f'{_ast2nat_wrap (ast.obj, 0, ast.obj.is_neg_num or ast.obj.op in {",", "=", "lamb", "piece", "+", "*", "/", "-", "diff", "intg", "lim", "sum"})}[{_ast2nat (_tuple2ast (ast.idx))}]',

	'text': lambda ast: ast.nat,
}

#...............................................................................................
def ast2py (ast): # abstract syntax tree -> Python code text
	return _ast2py_funcs [ast.op] (ast)

def _ast2py_curly (ast):
	return \
			_ast2py_paren (ast) \
			if ast.strip_minus ().op in {',', '+', '*', '/'} or (ast.is_log and ast.base is not None) else \
			ast2py (ast)

def _ast2py_paren (ast):
	return ast2py (ast) if ast.is_paren else f'({ast2py (ast)})'

def _ast2py_div (ast):
	n = _ast2py_curly (ast.numer)
	d = _ast2py_curly (ast.denom)

	return f'{n}{" / " if ast.numer.strip_minus ().op not in {"#", "@"} or ast.denom.strip_minus ().op not in {"#", "@"} else "/"}{d}'

def _ast2py_pow (ast):
	b = _ast2py_paren (ast.base) if _ast_is_neg (ast.base) else _ast2py_curly (ast.base)
	e = _ast2py_curly (ast.exp)

	return f'{b}**{e}'

def _ast2py_log (ast):
	return \
			f'ln{_ast2py_paren (ast.log)}' \
			if ast.base is None else \
			f'log{_ast2py_paren (ast.log)} / log{_ast2py_paren (ast.base)}' \

def _ast2py_lim (ast):
	return \
		f'''Limit({ast2py (ast.lim)}, {ast2py (ast.lvar)}, {ast2py (ast.to)}''' \
		f'''{", dir='+-'" if ast.dir is None else ", dir='-'" if ast.dir == '-' else ""})'''

def _ast2py_diff (ast):
	args = sum ((
			(ast2py (n.as_var),) \
			if n.is_var else \
			(ast2py (n.base.as_var), str (n.exp.num)) \
			for n in ast.dvs \
			), ())

	return f'Derivative({ast2py (ast.diff)}, {", ".join (args)})'

def _ast2py_intg (ast):
	if ast.from_ is None:
		return \
				f'Integral(1, {ast2py (ast.dv.as_var)})' \
				if ast.intg is None else \
				f'Integral({ast2py (ast.intg)}, {ast2py (ast.dv.as_var)})'
	else:
		return \
				f'Integral(1, ({ast2py (ast.dv.as_var)}, {ast2py (ast.from_)}, {ast2py (ast.to)}))' \
				if ast.intg is None else \
				f'Integral({ast2py (ast.intg)}, ({ast2py (ast.dv.as_var)}, {ast2py (ast.from_)}, {ast2py (ast.to)}))'

_ast2py_funcs = {
	'=': lambda ast: f'{_ast2py_paren (ast.lhs) if (ast.is_eq and ast.lhs.is_lamb) else ast2py (ast.lhs)} {ast.rel} {ast2py (ast.rhs)}',
	'#': lambda ast: ast.num,
	'@': lambda ast: ast.var,
	'.': lambda ast: f'{ast2py (ast.obj)}.{ast.attr}' if ast.args is None else f'{ast2py (ast.obj)}.{ast.attr}{_ast2py_paren (_tuple2ast (ast.args))}',
	'"': lambda ast: repr (ast.str_),
	',': lambda ast: f'{", ".join (ast2py (parm) for parm in ast.commas)}{_trail_comma (ast.commas)}',
	'(': lambda ast: f'({ast2py (ast.paren)})',
	'[': lambda ast: f'[{", ".join (ast2py (b) for b in ast.brack)}]',
	'|': lambda ast: f'abs({ast2py (ast.abs)})',
	'-': lambda ast: f'-{_ast2py_paren (ast.minus)}' if ast.minus.is_add else f'-{ast2py (ast.minus)}',
	'!': lambda ast: f'factorial({ast2py (ast.fact)})',
	'+': lambda ast: ' + '.join (ast2py (n) for n in ast.adds).replace (' + -', ' - '),
	'*': lambda ast: '*'.join (_ast2py_paren (n) if n.is_add else ast2py (n) for n in ast.muls),
	'/': _ast2py_div,
	'^': _ast2py_pow,
	'log': _ast2py_log,
	'sqrt': lambda ast: f'sqrt{_ast2py_paren (ast.rad)}' if ast.idx is None else ast2py (AST ('^', ast.rad.strip_paren (1), ('/', AST.One, ast.idx))),
	'func': lambda ast: f'{ast.unescaped}({ast2py (_tuple2ast (ast.args))})',
	'lim': _ast2py_lim,
	'sum': lambda ast: f'Sum({ast2py (ast.sum)}, ({ast2py (ast.svar)}, {ast2py (ast.from_)}, {ast2py (ast.to)}))',
	'diff': _ast2py_diff,
	'intg': _ast2py_intg,
	'vec': lambda ast: 'Matrix([' + ', '.join (f'[{ast2py (e)}]' for e in ast.vec) + '])',
	'mat': lambda ast: 'Matrix([' + ', '.join (f'[{", ".join (ast2py (e) for e in row)}]' for row in ast.mat) + '])',
	'piece': lambda ast: 'Piecewise(' + ', '.join (f'({ast2py (p [0])}, {True if p [1] is True else ast2py (p [1])})' for p in ast.pieces) + ')',
	'lamb': lambda ast: f'lambda{" " + ", ".join (v.var for v in ast.vars) if ast.vars else ""}: {ast2py (ast.lamb)}',
	'idx': lambda ast: f'{_ast2py_paren (ast.obj) if ast.obj.is_neg_num or ast.obj.op in {",", "=", "lamb", "piece", "+", "*", "/", "-", "diff", "intg", "lim", "sum"} else ast2py (ast.obj)}[{ast2py (_tuple2ast (ast.idx))}]',

	'text': lambda ast: ast.py,
}

#...............................................................................................
# Potentially bad __builtins__: eval, exec, globals, locals, vars, hasattr, getattr, setattr, delattr, exit, help, input, license, open, quit, __import__
_builtins_dict               = __builtins__ if isinstance (__builtins__, dict) else __builtins__.__dict__ # __builtins__.__dict__ if __name__ == '__main__' else __builtins__
_ast2spt_func_builtins_names = ['abs', 'all', 'any', 'ascii', 'bin', 'callable', 'chr', 'dir', 'divmod', 'format', 'hash', 'hex', 'id',
		'isinstance', 'issubclass', 'iter', 'len', 'max', 'min', 'next', 'oct', 'ord', 'pow', 'print', 'repr', 'round', 'sorted', 'sum', 'bool',
		'bytearray', 'bytes', 'complex', 'dict', 'enumerate', 'filter', 'float', 'frozenset', 'property', 'int', 'list', 'map', 'object', 'range',
		'reversed', 'set', 'slice', 'str', 'tuple', 'type', 'zip']

_ast2spt_func_builtins       = dict (no for no in filter (lambda no: no [1], ((n, _builtins_dict.get (n)) for n in _ast2spt_func_builtins_names)))

_ast2spt_consts              = { # 'e' and 'i' dynamically set on use from AST.E or I
	'pi'   : sp.pi,
	'oo'   : sp.oo,
	'zoo'  : sp.zoo,
	'None' : None,
	'True' : sp.boolalg.true,
	'False': sp.boolalg.false,
	'nan'  : sp.nan,
}

class ast2spt:
	def __init__ (self): self.kw = {} # never reached, here to make pylint calm down
	def __new__ (cls, ast):
		self    = super ().__new__ (cls)
		self.kw = {}

		spt     = self._ast2spt (ast)

		if callable (getattr (spt, 'doit', None)): # and spt.__class__ != sp.Piecewise
			try:
				spt = spt.doit ()
				spt = sp.piecewise_fold (spt) # prevent SymPy infinite piecewise recursion
			except:
				pass

		return spt

	def _ast2spt (self, ast): # abstract syntax tree -> sympy tree (expression)
		return self._ast2spt_funcs [ast.op] (self, ast)

	def _ast2spt_var (self, ast):
		spt = {**_ast2spt_consts, AST.E.var: sp.E, AST.I.var: sp.I}.get (ast.var, None)

		if spt is None:
			if len (ast.var) > 1 and ast.var not in AST.Var.GREEK:
				spt = getattr (sp, ast.var, None)

			if spt is None:
				spt = sp.Symbol (ast.var, **self.kw)

		return spt

	def _ast2spt_attr (self, ast):
		mbr = getattr (self._ast2spt (ast.obj), ast.attr)

		return mbr if ast.args is None else _ast_func_call (mbr, ast.args, self._ast2spt)

	def _ast2spt_func (self, ast):
		if ast.func == AST.Func.NOREMAP: # special reference meta-function
			return self._ast2spt (ast.args [0])

		if ast.func == AST.Func.NOEVAL: # special stop evaluation meta-function
			self.kw ['evaluate'] = False

			return ExprDontDoIt (self._ast2spt (ast.args [0]), self._ast2spt (ast.args [1]) if len (ast.args) > 1 else sp.S.One)

		func = getattr (sp, ast.unescaped, _ast2spt_func_builtins.get (ast.unescaped))

		if func is None:
			raise NameError (f'function {ast.unescaped!r} is not defined')

		return _ast_func_call (func, ast.args, self._ast2spt, is_escaped = ast.is_escaped, **self.kw)

	def _ast2spt_diff (self, ast):
		args = sum ((
				(self._ast2spt (n.as_var),) \
				if n.is_var else \
				(self._ast2spt (n.base.as_var), sp.Integer (n.exp.num)) \
				for n in ast.dvs \
				), ())

		return sp.Derivative (self._ast2spt (ast [1]), *args, **self.kw)

	def _ast2spt_intg (self, ast):
		if ast.from_ is None:
			return \
					sp.Integral (1, self._ast2spt (ast.dv.as_var)) \
					if ast.intg is None else \
					sp.Integral (self._ast2spt (ast.intg), self._ast2spt (ast.dv.as_var))
		else:
			return \
					sp.Integral (1, (self._ast2spt (ast.dv.as_var), self._ast2spt (ast.from_), self._ast2spt (ast.to))) \
					if ast.intg is None else \
					sp.Integral (self._ast2spt (ast [1]), (self._ast2spt (ast.dv.as_var), self._ast2spt (ast.from_), self._ast2spt (ast.to)))

	_ast2spt_eq = {
		'=':  sp.Eq,
		'==': sp.Eq,
		'!=': sp.Ne,
		'<':  sp.Lt,
		'<=': sp.Le,
		'>':  sp.Gt,
		'>=': sp.Ge,
	}

	_ast2spt_funcs = {
		'=': lambda self, ast: self._ast2spt_eq [ast.rel] (self._ast2spt (ast.lhs), self._ast2spt (ast.rhs)),
		'#': lambda self, ast: sp.Integer (ast [1]) if ast.is_int_text (ast.num) else sp.Float (ast.num, _SYMPY_FLOAT_PRECISION),
		'@': _ast2spt_var,
		'.': _ast2spt_attr,
		'"': lambda self, ast: ast.str_,
		',': lambda self, ast: tuple (self._ast2spt (p) for p in ast.commas),
		'(': lambda self, ast: self._ast2spt (ast.paren),
		'[': lambda self, ast: [self._ast2spt (b) for b in ast.brack],
		'|': lambda self, ast: sp.Abs (self._ast2spt (ast.abs), **self.kw),
		'-': lambda self, ast: -self._ast2spt (ast.minus),
		'!': lambda self, ast: sp.factorial (self._ast2spt (ast.fact), **self.kw),
		'+': lambda self, ast: sp.Add (*(self._ast2spt (n) for n in ast.adds), **self.kw),
		'*': lambda self, ast: sp.Mul (*(self._ast2spt (n) for n in ast.muls), **self.kw),
		'/': lambda self, ast: sp.Mul (self._ast2spt (ast.numer), sp.Pow (self._ast2spt (ast.denom), -1), **self.kw),
		'^': lambda self, ast: sp.Pow (self._ast2spt (ast.base), self._ast2spt (ast.exp), **self.kw),
		'log': lambda self, ast: sp.log (self._ast2spt (ast.log), **self.kw) if ast.base is None else sp.log (self._ast2spt (ast.log), self._ast2spt (ast.base), **self.kw),
		'sqrt': lambda self, ast: sp.Pow (self._ast2spt (ast.rad), sp.Pow (2, -1), **self.kw) if ast.idx is None else sp.Pow (self._ast2spt (ast.rad), sp.Pow (self._ast2spt (ast.idx), -1, **self.kw), **self.kw),
		'func': _ast2spt_func,
		'lim': lambda self, ast: (sp.Limit if ast.dir else sp.limit) (self._ast2spt (ast.lim), self._ast2spt (ast.lvar), self._ast2spt (ast.to), dir = ast.dir or '+-'),
		'sum': lambda self, ast: sp.Sum (self._ast2spt (ast.sum), (self._ast2spt (ast.svar), self._ast2spt (ast.from_), self._ast2spt (ast.to))),
		'diff': _ast2spt_diff,
		'intg': _ast2spt_intg,
		'vec': lambda self, ast: sp.Matrix ([[self._ast2spt (e)] for e in ast.vec], **self.kw),
		'mat': lambda self, ast: sp.Matrix ([[self._ast2spt (e) for e in row] for row in ast.mat], **self.kw),
		'piece': lambda self, ast: sp.Piecewise (*((self._ast2spt (p [0]), True if p [1] is True else self._ast2spt (p [1])) for p in ast.pieces), **self.kw),
		'lamb': lambda self, ast: sp.Lambda (tuple (self._ast2spt (v) for v in ast.vars), self._ast2spt (ast.lamb)),
		'idx': lambda self, ast: self._ast2spt (ast.obj) [self._ast2spt (ast.idx [0]) if len (ast.idx) == 1 else tuple (self._ast2spt (i) for i in ast.idx)],

		'text': lambda self, ast: ast.spt,
	}

#...............................................................................................
def spt2ast (spt): # sympy tree (expression) -> abstract syntax tree
	for cls in spt.__class__.__mro__:
		func = _spt2ast_funcs.get (cls)

		if func:
			return func (spt)

	tex = sp.latex (spt)

	if tex [0] == '<' and tex [-1] == '>': # for Python repr style of objects <class something> TODO: Move this to javascript.
		tex = '\\text{' + tex.replace ("<", "&lt;").replace (">", "&gt;").replace ("\n", "") + '}'

	return AST ('text', tex, str (spt), str (spt), spt)

_rec_num_deconstructed = re.compile (r'^(-?)(\d*[^0.e])?(0*)(?:(\.)(0*)(\d*[^0e])?(0*))?(?:([eE])([+-]?\d+))?$') # -101000.000101000e+123 -> (-) (101) (000) (.) (000) (101) (000) (e) (+123)

def _spt2ast_num (spt):
	m = _rec_num_deconstructed.match (str (spt))
	g = [g or '' for g in m.groups ()]

	if g [5]:
		return AST ('#', ''.join (g [:6] + g [7:]))

	e = len (g [2]) + (int (g [8]) if g [8] else 0)

	return AST ('#', \
			f'{g [0]}{g [1]}e+{e}'     if e >= 16 else \
			f'{g [0]}{g [1]}{"0" * e}' if e >= 0 else \
			f'{g [0]}{g [1]}e{e}')

def _spt2ast_MatrixBase (spt):
	return \
			AST ('mat', tuple (tuple (spt2ast (e) for e in spt [row, :]) for row in range (spt.rows))) \
			if spt.cols > 1 else \
			AST ('vec', tuple (spt2ast (e) for e in spt)) \
			if spt.rows > 1 else \
 			spt2ast (spt [0])

def _spt2ast_Add (spt):
	args = spt._sorted_args

	for arg in args:
		if isinstance (arg, sp.Order):
			break
	else:
		args = args [::-1]

	return AST ('+', tuple (spt2ast (arg) for arg in args))

def _spt2ast_Mul (spt):
	if spt.args [0] == -1:
		return AST ('-', spt2ast (sp.Mul (*spt.args [1:])))

	if spt.args [0].is_negative and isinstance (spt, sp.Number):
		return AST ('-', spt2ast (sp.Mul (-spt.args [0], *spt.args [1:])))

	numer = []
	denom = []

	for arg in spt.args:
		if isinstance (arg, sp.Pow) and arg.args [1].is_negative:
			denom.append (spt2ast (sp.Pow (arg.args [0], -arg.args [1])))
		else:
			numer.append (spt2ast (arg))

	if not denom:
		return AST ('*', tuple (numer)) if len (numer) > 1 else numer [0]

	if not numer:
		return AST ('/', AST.One, AST ('*', tuple (denom)) if len (denom) > 1 else denom [0])

	return AST ('/', AST ('*', tuple (numer)) if len (numer) > 1 else numer [0], \
			AST ('*', tuple (denom)) if len (denom) > 1 else denom [0])

def _spt2ast_Pow (spt):
	if spt.args [1].is_negative:
		return AST ('/', AST.One, spt2ast (sp.Pow (spt.args [0], -spt.args [1])))

	if spt.args [1] == 0.5:
		return AST ('sqrt', spt2ast (spt.args [0]))

	return AST ('^', spt2ast (spt.args [0]), spt2ast (spt.args [1]))

def _spt2ast_MatPow (spt):
	try: # compensate for some MatPow.doit() != mat**pow
		return spt2ast (spt.args [0] ** spt.args [1])
	except:
		return AST ('^', spt2ast (spt.args [0]), spt2ast (spt.args [1]))

def _spt2ast_Function (spt):
	return AST ('func', \
			f'{AST.Func.ESCAPE}{spt.__class__.__name__}' \
			if getattr (spt, '_SYMPAD_ESCAPED', None) else \
			spt.__class__.__name__ \
			, tuple (spt2ast (arg) for arg in spt.args))

def _spt2ast_Integral (spt):
	return \
			AST ('intg', spt2ast (spt.args [0]), AST ('@', f'd{spt2ast (spt.args [1] [0]) [1]}'), spt2ast (spt.args [1] [1]), spt2ast (spt.args [1] [2])) \
			if len (spt.args [1]) == 3 else \
			AST ('intg', spt2ast (spt.args [0]), AST ('@', f'd{spt2ast (spt.args [1] [0]) [1]}'))

_spt2ast_Limit_dirs = {'+': ('+',), '-': ('-',), '+-': ()}

_spt2ast_funcs = {
	ExprDontDoIt: lambda spt: AST ('func', AST.Func.NOEVAL, (spt2ast (spt.args [0]), spt2ast (spt.args [1]))),

	None.__class__: lambda spt: AST.None_,
	True.__class__: lambda spt: AST.True_,
	False.__class__: lambda spt: AST.False_,
	int: lambda spt: AST ('#', str (spt)),
	str: lambda spt: AST ('"', spt),
	tuple: lambda spt: AST ('(', (',', tuple (spt2ast (e) for e in spt))),
	list: lambda spt: AST ('[', tuple (spt2ast (e) for e in spt)),
	bool: lambda spt: AST.True_ if spt else AST.False_,
	sp.Tuple: lambda spt: spt2ast (spt.args),

	sp.Integer: _spt2ast_num,
	sp.Float: _spt2ast_num,
	sp.Rational: lambda spt: AST ('/', ('#', str (spt.p)), ('#', str (spt.q))) if spt.p >= 0 else AST ('-', ('/', ('#', str (-spt.p)), ('#', str (spt.q)))),
	sp.numbers.ImaginaryUnit: lambda ast: AST.I,
	sp.numbers.Pi: lambda spt: AST.Pi,
	sp.numbers.Exp1: lambda spt: AST.E,
	sp.numbers.Infinity: lambda spt: AST.Infty,
	sp.numbers.NegativeInfinity: lambda spt: AST ('-', AST.Infty),
	sp.numbers.ComplexInfinity: lambda spt: AST.CInfty,
	sp.numbers.NaN: lambda spt: AST.NaN,
	sp.Symbol: lambda spt: AST ('@', spt.name),

	sp.boolalg.BooleanTrue: lambda spt: AST.True_,
	sp.boolalg.BooleanFalse: lambda spt: AST.False_,
	sp.Eq: lambda spt: AST ('=', '=', spt2ast (spt.args [0]), spt2ast (spt.args [1])),
	sp.Ne: lambda spt: AST ('=', '!=', spt2ast (spt.args [0]), spt2ast (spt.args [1])),
	sp.Lt: lambda spt: AST ('=', '<', spt2ast (spt.args [0]), spt2ast (spt.args [1])),
	sp.Le: lambda spt: AST ('=', '<=', spt2ast (spt.args [0]), spt2ast (spt.args [1])),
	sp.Gt: lambda spt: AST ('=', '>', spt2ast (spt.args [0]), spt2ast (spt.args [1])),
	sp.Ge: lambda spt: AST ('=', '>=', spt2ast (spt.args [0]), spt2ast (spt.args [1])),

	sp.fancysets.Complexes: lambda spt: AST.Complexes,

	sp.matrices.MatrixBase: _spt2ast_MatrixBase,

	sp.Add: _spt2ast_Add,
	sp.Mul: _spt2ast_Mul,
	sp.Pow: _spt2ast_Pow,
	sp.MatPow: _spt2ast_MatPow,

	sp.Abs: lambda spt: AST ('|', spt2ast (spt.args [0])),
	sp.arg: lambda spt: AST ('func', 'arg', (spt2ast (spt.args [0]),)),
	sp.exp: lambda spt: AST ('^', AST.E, spt2ast (spt.args [0])),
	sp.factorial: lambda spt: AST ('!', spt2ast (spt.args [0])),
	sp.Function: _spt2ast_Function,
	sp.functions.elementary.trigonometric.TrigonometricFunction: _spt2ast_Function,
	sp.functions.elementary.hyperbolic.HyperbolicFunction: _spt2ast_Function,
	sp.functions.elementary.trigonometric.InverseTrigonometricFunction: _spt2ast_Function,
	sp.functions.elementary.hyperbolic.InverseHyperbolicFunction: _spt2ast_Function,
	sp.log: lambda spt: AST ('log', spt2ast (spt.args [0])) if len (spt.args) == 1 else AST ('log', spt2ast (spt.args [0]), spt2ast (spt.args [1])),
	sp.Min: lambda spt: AST ('func', 'Min', ((spt2ast (spt.args [0]) if len (spt.args) == 1 else spt2ast (spt.args)),)),
	sp.Max: lambda spt: AST ('func', 'Max', ((spt2ast (spt.args [0]) if len (spt.args) == 1 else spt2ast (spt.args)),)),

	sp.Limit: lambda spt: AST (*(('lim', spt2ast (spt.args [0]), spt2ast (spt.args [1]), spt2ast (spt.args [2])) + _spt2ast_Limit_dirs [spt.args [3].name])),
	sp.Sum: lambda spt: AST ('sum', spt2ast (spt.args [0]), spt2ast (spt.args [1] [0]), spt2ast (spt.args [1] [1]), spt2ast (spt.args [1] [2])),
	sp.Integral: _spt2ast_Integral,

	sp.Order: lambda spt: AST ('func', 'O', ((spt2ast (spt.args [0]) if spt.args [1] [1] == 0 else spt2ast (spt.args)),)),
	sp.Piecewise: lambda spt: AST ('piece', tuple ((spt2ast (t [0]), True if isinstance (t [1], sp.boolalg.BooleanTrue) else spt2ast (t [1])) for t in spt.args)),
	sp.Lambda: lambda spt: AST ('lamb', spt2ast (spt.args [1]), tuple (spt2ast (v) for v in spt.args [0])),
}

#...............................................................................................
def set_precision (ast): # recurse through ast to set sympy float precision according to longest string of digits found
	global _SYMPY_FLOAT_PRECISION

	prec  = 15
	stack = [ast]

	while stack:
		ast = stack.pop ()

		if not isinstance (ast, AST):
			pass # nop
		elif ast.is_num:
			prec = max (prec, len (ast.num)) # will be a little more than number of digits to compensate for falling precision with some calculations
		else:
			stack.extend (ast [1:])

	_SYMPY_FLOAT_PRECISION = prec if prec > 15 else None

def set_user_funcs (user_funcs):
	global _USER_FUNCS

	_USER_FUNCS = user_funcs

class sym: # for single script
	AST_Text       = AST_Text
	set_precision  = set_precision
	set_user_funcs = set_user_funcs
	ast2tex        = ast2tex
	ast2nat        = ast2nat
	ast2py         = ast2py
	ast2spt        = ast2spt
	spt2ast        = spt2ast

# if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: ## DEBUG!
# 	ast = AST ('func', 'Piecewise', (('(', (',', (('#', '1'), ('#', '2')))),))
# 	res = ast2py (ast)
# 	print (res)
# Builds expression tree from text, nodes are nested AST tuples.
#
# Time and interest permitting:
# sets
# var assumptions
# importing modules to allow custom code execution
# Proper implementation of vectors with "<b>\vec{x}</b>" and "<b>\hat{i}</b>" variables
# systems of equations, ODEs, graphical plots (using matplotlib?)...

import ast as py_ast
from collections import OrderedDict
import os
import re
import sys


def _FUNC_name (FUNC):
	return AST.Func.TEX2PY_TRIGHINV.get (FUNC.grp [1], FUNC.grp [1]) if FUNC.grp [1] else \
			FUNC.grp [0] or FUNC.grp [2] or FUNC.grp [3].replace ('\\', '') or FUNC.text

def _ast_from_tok_digit_or_var (tok, i = 0):
	return AST ('#', tok.grp [i]) if tok.grp [i] else \
			AST ('@', AST.Var.ANY2PY.get (tok.grp [i + 2].replace (' ', ''), tok.grp [i + 1]) if tok.grp [i + 2] else tok.grp [i + 1])

def _ast_func_tuple_args (ast):
	ast = ast.strip (1)

	return ast.commas if ast.is_comma else (ast,)

def _ast_func_reorder (ast):
	wrap = None

	if ast.is_fact:
		ast2, wrap = ast.fact, lambda a: AST ('!', a)
	elif ast.is_pow:
		ast2, wrap = ast.base, lambda a: AST ('^', a, ast.exp)
	elif ast.is_attr:
		ast2, wrap = ast.obj, lambda a: AST ('.', a, *ast [2:])

	if wrap:
		ast3, wrap2 = _ast_func_reorder (ast2)

		if ast3.is_paren:
			return ast3, lambda a: wrap (wrap2 (a))

	return ast, lambda a: a

#...............................................................................................
def _expr_lambda (lhs, expr):
	if lhs.is_var:
		return AST ('lamb', expr, (lhs,))

	elif lhs.is_comma:
		for var in lhs.commas:
			if not var.is_var:
				break
		else:
			return AST ('lamb', expr, lhs.commas)

	raise SyntaxError ('invalid lambda function')

def _expr_mul_imp (lhs, rhs, user_funcs = {}):
	last      = lhs.muls [-1] if lhs.is_mul else lhs
	arg, wrap = _ast_func_reorder (rhs)
	ast       = None

	if last.is_attr: # {x.y} * () -> x.y(), x.{y.z} -> {x.y}.z
		if last.args is None:
			if arg.is_paren:
				ast = wrap (AST ('.', last.obj, last.attr, _ast_func_tuple_args (arg)))
			elif rhs.is_attr:
				ast = AST ('.', _expr_mul_imp (last, rhs.obj), rhs.attr)

	elif last.is_pow: # {x^y.z} * () -> x^{y.z()}
		if last.exp.is_attr and last.exp.args is None:
			if arg.is_paren:
				ast = AST ('^', last.base, wrap (AST ('.', last.exp.obj, last.exp.attr, _ast_func_tuple_args (arg))))
			elif rhs.is_attr:
				ast = AST ('^', last.base, ('.', _expr_mul_imp (last.exp, rhs.obj), rhs.attr))

	elif last.is_var: # user_func * () -> user_func ()
		if last.var in user_funcs:
			if arg.is_paren:
				ast = wrap (AST ('func', last.var, _ast_func_tuple_args (arg)))
			elif arg.is_attr and arg.obj.is_paren:
				ast = wrap (AST ('func', last.var, _ast_func_tuple_args (arg.obj)))

	if arg.is_brack: # x * [y] -> x [y]
		if not arg.brack:
			raise SyntaxError ('missing index')

		ast = wrap (AST ('idx', last, arg.brack))

	if ast:
		return AST ('*', lhs.muls [:-1] + (ast,)) if lhs.is_mul else ast

	return AST.flatcat ('*', lhs, rhs)

def _expr_diff (ast): # convert possible cases of derivatives in ast: ('*', ('/', 'd', 'dx'), expr) -> ('diff', expr, 'dx')
	def _interpret_divide (ast):
		if ast.numer.is_diff_or_part_solo:
			p = 1
			v = ast.numer

		elif ast.numer.is_pow and ast.numer.base.is_diff_or_part_solo and ast.numer.exp.remove_curlys ().is_pos_int:
			p = int (ast.numer.exp.remove_curlys ().num)
			v = ast.numer.base

		else:
			return None

		ast_dv_check = (lambda n: n.is_differential) if v.is_diff_solo else (lambda n: n.is_partial)

		ns = ast.denom.muls if ast.denom.is_mul else (ast.denom,)
		ds = []
		cp = p

		for i in range (len (ns)):
			n = ns [i]

			if ast_dv_check (n):
				dec = 1
			elif n.is_pow and ast_dv_check (n.base) and n.exp.remove_curlys ().is_pos_int:
				dec = int (n.exp.remove_curlys ().num)
			else:
				return None

			cp -= dec

			if cp < 0:
				return None # raise SyntaxError?

			ds.append (n)

			if not cp:
				if i == len (ns) - 1:
					return AST ('diff', None, tuple (ds))
				elif i == len (ns) - 2:
					return AST ('diff', ns [-1], tuple (ds))
				else:
					return AST ('diff', AST ('*', ns [i + 1:]), tuple (ds))

		return None # raise SyntaxError?

	# start here
	if ast.is_div: # this part handles d/dx
		diff = _interpret_divide (ast)

		if diff and diff [1]:
			return diff

	elif ast.is_mul: # this part needed to handle \frac{d}{dx}
		tail = []
		end  = len (ast.muls)

		for i in range (end - 1, -1, -1):
			if ast.muls [i].is_div:
				diff = _interpret_divide (ast.muls [i])

				if diff:
					if diff.expr:
						if i < end - 1:
							tail [0 : 0] = ast.muls [i + 1 : end]

						tail.insert (0, diff)

					elif i < end - 1:
						tail.insert (0, AST ('diff', ast.muls [i + 1] if i == end - 2 else AST ('*', ast.muls [i + 1 : end]), diff.dvs))

					else:
						continue

					end = i

		if tail:
			tail = tail [0] if len (tail) == 1 else AST ('*', tuple (tail))

			return tail if end == 0 else AST.flatcat ('*', ast.muls [0], tail) if end == 1 else AST.flatcat ('*', AST ('*', ast.muls [:end]), tail)

	return ast

def _ast_strip_tail_differential (ast):
	if ast.is_differential or ast.is_null_var: # null_var is for autocomplete
		return None, ast

	if ast.is_intg:
		if ast.intg is not None:
			ast2, neg = ast.intg.strip_minus (retneg = True)
			ast2, dv  = _ast_strip_tail_differential (ast2)

			if dv:
				return \
						(AST ('intg', neg (ast2), dv, *ast [3:]), ast.dv) \
						if ast2 else \
						(AST ('intg', neg (AST.One), dv, *ast [3:]), ast.dv) \
						if neg.has_neg else \
						(AST ('intg', None, dv, *ast [3:]), ast.dv)

	elif ast.is_diff:
		ast2, neg = ast.diff.strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv:
			return \
					(AST ('diff', neg (ast2), ast.dvs), dv) \
					if ast2 else \
					(neg (AST ('/', ('@', ast.diff_type or 'd'), ast.dvs [0])), dv) \
					if len (ast.dvs) == 1 else \
					(neg (AST ('/', ('@', ast.diff_type or 'd'), ('*', ast.dvs))), dv)

	elif ast.is_div:
		ast2, neg = ast.denom.strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv and ast2:
			return AST ('/', ast.numer, neg (ast2)), dv

		ast2, neg = ast.numer.strip_minus (retneg = True)

		if dv:
			return AST ('/', neg (ast2) if ast2 else neg (AST.One), ast.denom), dv

	elif ast.is_mul:
		ast2, neg = ast.muls [-1].strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv:
			return \
					(AST ('*', ast.muls [:-1] + (neg (ast2),)), dv) \
					if ast2 else \
					(neg (AST ('*', ast.muls [:-1])), dv) \
					if len (ast.muls) > 2 else \
					(neg (ast.muls [0]), dv)

	elif ast.is_add:
		ast2, neg = ast.adds [-1].strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv and ast2:
			return AST ('+', ast.adds [:-1] + (neg (ast2),)), dv

	return ast, None

def _expr_intg (ast, from_to = ()): # find differential for integration if present in ast and return integral ast
	ast, neg = ast.strip_minus (retneg = True)
	ast, dv  = _ast_strip_tail_differential (ast)

	if dv:
		return \
				AST ('intg', neg (ast), dv, *from_to) \
				if ast else \
				AST ('intg', neg (AST.One), dv, *from_to) \
				if neg.has_neg else \
				neg (AST ('intg', None, dv, *from_to))

	raise SyntaxError ('integration expecting a differential')

def _expr_func (iparm, *args, strip = 1): # rearrange ast tree for explicit parentheses like func (x)^y to give (func (x))^y instead of func((x)^y)
	ast, wrap = _ast_func_reorder (args [iparm])

	return wrap (AST (*(args [:iparm] + ((_ast_func_tuple_args (ast) if args [0] == 'func' else ast.strip (strip)),) + args [iparm + 1:])))

def _expr_func_func (FUNC, expr_neg_func):
	func = _FUNC_name (FUNC) if isinstance (FUNC, lalr1.Token) else FUNC

	return _expr_func (2, 'func', func, expr_neg_func)

def _expr_mat (expr_mat_rows):
	return \
			AST.MatEmpty \
			if not expr_mat_rows else \
			AST ('mat', expr_mat_rows) \
			if len (expr_mat_rows [0]) > 1 else  \
			AST ('vec', tuple (c [0] for c in expr_mat_rows))

def _expr_curly (ast): # convert curly expression to vector or matrix if appropriate
	if not ast.is_comma:
		return AST ('{', ast)
	elif not ast.commas: # empty {}?
		return AST.VarNull

	c = sum (bool (c.is_vec) for c in ast.commas)

	if c == len (ast.commas) and len (set (len (c.vec) for c in ast.commas)) == 1:
		return \
				AST ('mat', tuple (c.vec for c in ast.commas)) \
				if len (ast.commas [0].vec) > 1 else \
				AST ('vec', tuple (c.vec [0] for c in ast.commas))

	return AST ('vec', ast.commas) # raise SyntaxError ('invalid matrix syntax')

#...............................................................................................
class Parser (lalr1.Parser):
	def __init__ (self):
		self.TOKENS_LONG.update ([(v, self.TOKENS [v]) for v in self.TOKENS_QUICK])

		lalr1.Parser.__init__ (self)

	def set_quick (self, yes = True):
		self.TOKENS.update (self.TOKENS_QUICK if yes else self.TOKENS_LONG)

		self.set_tokens (self.TOKENS)

	_USER_FUNCS = set () # set or dict of variable names to be translated into 'func' ASTs if variable followed by parentheses

	def set_user_funcs  (self, user_funcs):
		self._USER_FUNCS = user_funcs

	_PARSER_TABLES = \
			b'eJztXWuP3LaS/TMLZAZQAy2K1GO+2YmTa6zt5NpOsIuBYTiOcxFsXms7+8DF/vetqlN8Sj2t7umZ6ReG0xLJUpEs1qHIIileXH/xLx9+/+mL6osfHr2k32dPvn5Nl+8evXzy4hndPP3mxbcvn7z98vuXz/6dvF+/fPSlXmq9Gro+fvLN2y8fvXrySu+fP3qt' \
			b'd4/j7Q/x9jvcCldO5fnTF9/Ls8TvXzng1WvOzKvvH9Pvi++fc0ZevP6G8/f0uUTI799fMpdnL/jnW479+vsXnL3HUpQvv33+/JFcn337wpfppU/2pU+Ob14+/eZvzOrR8+/o96vHz149e/Tqb3T75MVXWhi+exxvf4i3Wpgnf+efZ6+eaLCXB3N7jQxRBpjy' \
			b'+aPvXr3+lpN7LcV88m9fPvPRLNWvnv7w9Ctm8+VX374WYcjjT19IEt89E1E9/Zp+hAtJiZ96/+7jh89v//j49qcff/30+d1HCvrwP39+fPvprz8/BM/vH/7x9ue/fn8fI3/0t7+9+/z2/R+/pt6Pf/x34f3k/e/fffrw6dP73Ptn7vW+dz/G28+fQ15+fvf+' \
			b's7//M6aUZ+83f/vrL+H2l98//yPk669f3/7yW0j49/jAT7/8l7/9/OFjEvzzz/7+x4/v3v/Hh8+JcEIB/vr46/+madBNIopQnJ9+yoocc/jhP0N5KJFQzF8+vP8QPFRhv0emf376/If3/Vesvl/f/fbjT++8L7ANyf7x22/vMs+nL95U1xcLW1fWXFa4afim' \
			b'qRZWrnV1YSrTVou6avjmMoRKWAxY9HxTN/hxhmLdZRpU2zSIb/nBJX4sIuiOeAlJzwnXThOmQB+qYSFgYZZyZ6oL8hCt1SjOAgph+KepGnupXvLJnZWiUtSiucwC4Gv8cxRvfRDf0p2Rf9P5R5mpJKvhyAPlTgPhbyn/jeR/6QOoDHI3EK0U3dT4sVw2ZR6D' \
			b'WIwxlG+53ujfVQ2xgBwt3zDFgB+LaqI7ErGkRnJnObKMzKUPaVNfp1cO4mc7qhAu5HCZeLkySEB1Ht7kXjv29nmQG3ntMg1aGMioVu2i9GrIoMYtk5EQWIjMm59WAh8cvQsjsnH0Dx3mBy4RtJBSUwYuzLKqu4orq62clVIyU9TrNAHDhxR/Fh1VY063ICjR' \
			b'HRV/0VfW+ixR2Qcpp1U8cAmpql2KCorzwSGAa45D2hhSI6SLIQYhvQ8hfRQt7/CTAKNT9W5a/AgmwIl8fMt3zkdeqpd8PgJpOPzYIZTdB7llGsS3LJgGP1Rvl5fxlmkoj5JjfYQyWIukCAUSodrDoDDgRfITNZKmpfFNGsgoTEKi10qdNR6ppCS1QGeA1jmJ' \
			b'ZEWDzNNgDSC/pNvjh7TyUv2ERMkbN2edMFavA2xJyATuoDZcBuifTXSm9QWjwAsboSneJnAlr0X56Vlj/F2rN3W4EaK2qi/pnXC9rEgnKQkCH8mcUCPNINWjI0dEy7Zq66o1Vd9WfVf1fdUP1bCshroaSLg955lTrrleCa9UpdTWESEpcNtUra1aV7XEpKva' \
			b'vuooqqu6nrFIjVRfVz1Vlqnw2qCC10vyLMm3pGpZOm5xWP+bqndVRw8sGXgkewKY6ypHgqRkKDddNRCa6J3QMKYsKV5L0uB2lDRwaKqBuJN8SdCUBrWvFWXqTXVBnkt6MZIIuAZNi0sjsuEGjL0NaBr1OQjuwuEZyezlSQvRtSqJFpKiorIfGnZBpZbQHlRt' \
			b'A2IJZeyJMEkoJy5EKg5UsT95SQyQxCDgvBigTYNRVWlEQCjSuDAoQ8h9mXXKMUmPErG1onrYCTdtRxyy7JBl0emLXvNdS3vBTT0xpfcPsRoqao5Pqm5rbSIGCAhNQtf5VkDkhkxS3kJedp2RTLapSG+pB9fc5z9t9FLrL+/JjmrNVh0lUVedqdqh6k5L1UkQ' \
			b'7iwICKI9CwKC6M6C4LdA26Pdx8XgZdCjR1hbfTHjVdrgVdrg7X8hGZW+ptWrU3J0Kzvhtf9vioseo4fedxxQLCelGGjw7yszVN3hvhUvnFapQ4fIodrdoOMD7eYhctBusNXxgQikJ0W0+1Icypvdx0xBoWwb8wY92p8cooZtn+SQHlxy81PvUTbRHA2AYsgg' \
			b'Rw1qAmj9UKTTRkgbJx1TuJPvA3LhYUihy2kVncpKZT6FsrIFzKi9h6v5hCqZSmVOHOKtYJvteKcuCXviEmDjrbQDVKwTa+7ZWmvUVmlgqzwxCYg91tzagnqdzQu8CdMqbJ81alml69GMia4vBDNHUZL+SErCFnrRtVq79WqeqHU2UOexaowPzFIHAZ30BQ63' \
			b'2Ndsfz/oEvC8gVQchmcTE41vMBspa3K4nW4tHujUaoQHu9pXKYwPrVooOlgoWgxq2hYXfek1kjYbqBgFhyKxzjerku18lOsgo3z2avCz3XLdZVaGNliHDKxDBtYhw7IfEGqN1rD2OqXemtjrwgsXfa/TeO32+2cZu+iBI2tRZ9qcWjSQe5VTq+i1/d7ljbA2' \
			b'7F3V0mtvudw18tnsp6Y2A7OagTVNGgBvQeLVaAzvS6y5aU7J0sCmlQavNCl/C3Gcp1h1NYERcVjIqMOll4vpITEqa4OBWcOvk0aDHYLzdxwYjBYlTIRyV7HRrqJBH5HHQCe3nkN6wwa94RMb+LJGNNCIBj0SRWajHUuDHiVdTg+Z19x3PjWFaB1UAHrRdtCE' \
			b'Bi34oUxMX/NIpjmckYwMYZojsgzxSMvoeKjBeKjBeIguvoPYJR6LlsdgKS2PCwzmgRtMtsrrb9Cule9bCUsqJ/oWVvsW1g+N8W618m61eKlafZvaE5ncMsBtPWiDDq83CbQa3EBKh4NupxnOOj6UXwtVs1A1q0Nvq2Nuu2fDEVZap0rr/GsXSutEafmXVNEp' \
			b'kBxK51A6d1ovJmkvTqzMrLQORsBWdaCFDrTQAbpQ3wxa3oKwU8LukG2h11zGDmXsBBKwVuuyayldau7jAveQTI+neiXsD14Mw4GXYDjsErASDbreb6kL/pbyvllWvO2MGiSkjzaFcyQJ8v6IpWyRwFS6LzdaL2Q/zSYX10pBey8SaeEYCGIZIfnxWjPLq+F4' \
			b'mSGbnTSvsmdpSRnk0nBxuDycDZ4D4gkgnubh3WGG/Lw1hwvOrRmvS+VFqbzulNeDsUh5ZwrvJ+G1i7xwkdcJ8rI8XtzJKzt5HSTvGuPWl9dCsmB4loI7FTzHwNMQbGdgIwOvjeXtECxM3gHD+ea1kcNAAsROWd4WiG2mvP+Sa2DheJ8rFYn3u1LLvqAKXVBj' \
			b'zvtQZUeh7KelOAqmelx0skGRyGQHdSW7srk2FyyeBctH9kFTHhY9P02BpGSLgbc4MmfZGlrJ1lzjs8BbGCnjnIOOtyk3yoj3Lfa825X/2S/bIYlw4Ick35Xs+uQNpy1vM5fdwBRfY6svbxulIN6eydt3mT+z4H2T/ASFtVxq3r/KT/PuW/Lz3uqBd2guuQDk' \
			b'uCzYPr7gvet9i83RxGLgbZfMjgXJ23Hp33HCwxvuCLLOttBUI2rvdDMPzD7GqL7GlSACkxS5N2lwE5WYZItXbsQ4FDogXd7bCsyWIckmBtH1YBSkCkPTwarfRO1nJRIA5KAFEDqAYUlllAaingAGl98koBgKMPB2WjcBCuIn26ELcPCCVV4ZKjveiY63UK0C' \
			b'jIDFJoBpFDQuAQ7F8apqDx6eDRQAER1PYvF0UwYmavYCaOSeQNMLZLC/vPeQ6ZO/mfDpA3j6DD6BTQGjfuIvwCoJAsD6ADFW8lYwhuiIs16QFjjleAOx4owxFvAlMQXGUO6IM2U6KPUqxPVK54xQtcArMAcZAHO9oM4zjdir/tleiQzs8oqbo6G7EtmS9lwx' \
			b'1Ekb6Gr+T3o5Z4zeNUbvFZtSuIBO9fViTmWAdtgoX4e3Gk+K1pmbC9T4muPbFKpNdCVcb3DdMgFuk3NR9DYBvkys+OVGoMkR3ADC8izY5ij2YpnCscYVSPaiSbAcMje4G6Gs+WMwNyWala3HM16jCeetMN0kmK4TWPcPD+iVaG5uBeijBbMYBDyYW5gHtJOq' \
			b'HVSJFyTXpnQzkSwcgWS+TZCcMSuRPEouknoYl+G9KAS3S6bo63osK13EsqTcRcYFkJV+EsiIK4GskolAjtlbB2RQOU0zB7LKCEAWsozzaiBPANhOvZT3Gb1n6I6h28gHavx7GL4Ut03AbVO6ubiNb+A6fwNnzErcjpKLpAG3RThev3WzArRKlIAWL+DAtQCt' \
			b'0k+CFnElaFUsCWhD3taBFlTOIM0ctCogBS3evgnnjUDrTgi0R92B5ocicOFLgdsF4HalmwvcLgK3y4GbMiuBO0oukgbgFuEK3C4Al289bJUkgW0H2CZsC+TqI5PIRVyJXJVLgtzAfR1yQeUM0syRqxJS5HZAbuS8Vb+5PSP4OBA8VPJVQ0UwfCmCh4DgkZuL' \
			b'4CEieMgRnDIrETyVYsitIrgIVwQPEcFDRLCSJAgegOCEbYFgfWQSwYgrEaxySRAcuK9DMKicQZo5glVCiuABCI6ct0Jwd0bwUSCYK2wZEKy+BMESKQhGXOpmIlg4AsEmn6jJmBUIHicXST2Cy3AgmO8UwSbarjxJRLAk2mVscwT7R6YQrHEFgr1cIoIj9zUI' \
			b'VipnkGaGYC8hIFjIMs5bIbg/26OPDMqG6yxAGT6CssEcq1yWIAGgTenmAjpasUxuxcqYlYAeJZdRB0wX4YrpaMXiW49pJUkwDRtWyrbAtD4yiWnElZhW0SSYDtzXYRpUTtPMMa1CUkzDjJVw3grTwxnTR4bpTj7u7jENH2O6A6Y7YDoMlEGRurmYjgNlkw+U' \
			b'M2YlpvO0WOYZeQB1kScFdRwsmzhY9iQJqDFYTtkWoNZHJkGNuBLUKpsE1IH7OlCDyuGz+wWoVUoKagyWE85bgbpenlF9ZKiWZWoB1fAxqrG0A19pBwlQ3ZduLqrjGg+TL/LImJWoHiWXUQdQF+EK6rjww8SVH54kATUWf6RsC1DrI5OgRlwJahVNAurAfR2o' \
			b'QeUM0sxBrUJSUGMpSMJ5O1Cfl2wdG6gHrp4Aavh6XBjUA0AdLGJm5OaCOlrETG4Ry5iVoJ5KMVIHUBfhCupoFDPRKOZJElDDKJayLUCtj0yCGnElqFU0CagD93WgBpUzSDMHtQpJQQ2jWMJ5O1Cf13gdGai5YqJ5TH39gFNQan8YShOMZKBI3UxQN9FI1uRG' \
			b'soxZAepxchm1B3UZDlA30U7WRDuZJ4mgbmAnS9nmoPaPTIFa4wpQe9FEUEfua0CtVHrCUQ5qLySAuoGdLOG8HaibHNTNYeM6+artGd5cIBvnr0SgHMCnfNhKT8iSiSwbJrJs6eZOZNk4kWXziayUWTmRNUouow5zWUW4zmXZOJdlBeF+FbvMaSlpMqdlMaeV' \
			b'sC/mtPSRyTktxJVzWiqiZE4rBK6b0wKVM0gzn9NSYemclsWcVuS8HdJvWA1WH+G81hxUl7uJNkX2HaGaj2RiFWGg3twrdxV2/6BXDl8yv9VpPLrkrnRb7ETip1JwSzXE/1G/fJRmTDx0yotwj25sY+pclS0S4/pbFqvElrpMzGdi1C9XxhHYzDV2zRFdds1V' \
			b'RPnuJg5a1zF3ssep8xnNe+bg6nvmXKmc4WqhJvKQmymQD3SVtTcEdgdQuxVrtPfq9b28q/Xax/z25qqKewpZWRDAg+4Wg+4Wg+42ILwt3dxBdxsB3hYANwm3Et2j9FLXJgtBy2zxAm45dtG0cezdRpArVTL2bjH2DhxGGNdHJsfemk4BcJVQMvYO3NdBHFQO' \
			b'x/YWCFdRKcJb4Dpy3u7lPbmmbK9Afh57bzb27rkOwtgbPuwCl7E3rORNsJKDInVzx97RSt7kVvKMWTn2HiWXUYexdxGuY+9oJW+ildyTJGNvWMlTtsXYWx+ZHHsjrhx7q2iSsXfgvm7sDSpnkGY+9lYh6dgbVvKE83agnlxmtnNQ518iOEP77qE9yGnCHtrw' \
			b'9bgwtGErb4KtvBm5udCOtvIB09qs0nyq01IRLtz4m1Vjk/k41SwHAeFFuCI8msybaDL3JAnCYTJP2RYI10cmEY64EuEqoQThgfs6hIPKGaSZI1zrRxEOk3nCeTuEn5ehHRm2We5xW7T6CNsy4IYPtaPYRljqZmJb+ALbfJu8tjNmBajHyWXUHtRlOEDNdwpq' \
			b'vlVQe5IIakm3y9jmoPaPTIFa4wpQe9FEUEfua0CtVM4gzQzUXkgAtZBlnLcD9eQ6tF2vDt+t5SyCNwXu1Md37gios0F6a4A2LMYAUPgSk5gN+yURl7q50IzmMJvvlxzBcZRETCtgsQhXLJZ7JKEea7/j45lMQg9xJfS06An0Yl5ugB0o/Id8EswhwmMOmyEj' \
			b'y802Q5rJ1WFnrO0J1hyPLgLW4EuxFmzPiEvdXKy5iDV3M9ZGScS0AtaKcMWam8Cam4E1ZTKJNcSVWNOiJ1iLebkBa6CYwBoiPNYcsBZYboi1yUVbZ6ztCda6ysa10upLsRZWSSMudXOxFldJ2+5mrI2SiGkFrBXhirVuAmvdDKwpk0msIa7EmhY9wVrMyw1Y' \
			b'A8UE1hDhsYbVz5HlhlibXEt1pDsMj3YsOLCEAyThSyEZLDx25OZCMlp4bL4aMmNWwnMqxZBbhWcRrvAcqslPc3iiZBAIy07gWsBV6SfhirgSriqWBK4hb+tGgKByBmnmqFUBKWph1kk4b4ba5ozag0ctyzYuelRfgloXljsiLnUzUevickeXL3fMmBWoHScX' \
			b'ST1qy3Cg1i2nUeuJImodVjsGrjlqPf0UajWuQK0XS0RtzNsa1CqVM0gzQ60XEFDrsNQx4bwZas+fwToC1NaVi3ZX9aWoDRZXxKVuLmqjxdXlFteMWYna1S6itghX1NYrUKtECWphcA1cC9Qq/SRqEVeiVsWSoDbkbR1qQeUM0sxRqwJS1MLamnDeDLWn9B2s' \
			b'o0WtYcEG1MKXojZs10dc6uaiNm7Xd/l2/YxZidpRcpE0oLYIV9Su+OKkJ0pQi936gWuBWqWfRC3iStSqWBLUhmTXoRZUPs0ctSogRS3WISacN0Ntu+p8gXRxYrv36453+xlZovGHGgi0lwW8+x0tR54Bczn4wMyEe78N5LtZ5yO0OD1DbVjFQQku2LJAk7ot' \
			b'1iy73JiVcRsdptDJgQrjdF1i2irDeTWjlcahtG75xkHpksahQ+PgGRc7EUSK7LcoM2Ry47kMyqpsNFRo+SpmDb2p1WClYT69CMwf2iC5yJoPPrvBy1KbEJjGoniKJoQH4MsriZPf/kp2Nzi5UFPiOmlJuur6zs8p2ZNDSuo1eG1usCP31erDSljo+3NOyT6d' \
			b'UcJS2eScklzfbzirhLJ092rLZ2kt90V5N1HcOUq7f6fr1Ol3FfdBe3d7wo506wwa3WFae80dKLA7AAXmc7PuTonNdO/nDhX5gI6KYllvd1wUyWhSicdjj9srcbdLJW4fsCWmeCpAVGYjG9MOQ6m7O1BqltiDtNAYYS2DcvtRVqnk9fx+BlXbrk7yozrZYu3F' \
			b'ffaV6xnKbu6o6zH/g3S3OdyvTrbXRAUvvip3xy032wtubr3b9YruVnRHqJKpQ2LlCCJzT91pbxfaUXPO1i6K45PB77WDPXdkuH+dbFhe9H+nzTl6cbXYve6v412LWGZ0vqnSrigx0famur4HewefYovWHAdPb6bm9zVu5Hdwv03Xez9UOh6BE9aZ1rLxoZyr' \
			b'n6XO9zJulPyRvLfoctv7UVw55lx1t7tb9Z2yu2+qwiyC9phUmQLjV6t5HmLRmbtV6YnP0G/cKhsuA68421q93Tz1JoXaiSk6PRV8S/WeM700Na20iYovH6il7mbvHtjWNl3LvlO7C/Xu3KatNnetNzKUqJpvr97tTPXud6TeQbeX99X52FS1j1OtU5Vmedxb' \
			b'R2RDlb6lOncz1XnYtTrXZ3V+OHVujlWd+5l965krZuarszmr88Opsz1WdR7uZai4lQXvvqfEzaZWu4aXse3LcHB749y9zoLz8rUN1nBU/+RFjU6Oz16eVfXATRY701FeLLkHKzWooq8ILqKd9f3Y3NrM7HZHarpqpeu2FrcDV1sWyqLuU2vbnTWzfM7xLq1s' \
			b'G/cIqCx3oMjmxpbWlcu676m9Xbs0e86EXqNKvNwbRcay9+XaNlhoysXR99VfWLPaecaaT/4ot3yRXYox6jc0VwRoaZrvZB7vrNH3qtG1/K/X6PqwNXpQja5v1mhbXetePOe1uBH9bURzg9rWqpj53rVmWn/aYtNJ77i+9RPubSUCGmLlcsW2WqM4vyGryT5b' \
			b'KtPFfVXylpsQIYsnFUvbyOvIzS5qhkQrvaLazSu633JXQqIQAWvZZiKopbSpsrYayXo3RyxuLBkbhNPOF46dlI/dCxlNgdrLyWP01rLq5stqsm1Hqz6/SZ8j03VbQEey9j3m5a1lbuR/ukFtEbdZIzqngtZsjCxrzh+5Upu8+eunqvJhhv4rNwVvOXa66QW9' \
			b'erx0oyZMv33loIuHGs5P7rPdesxzw4t15dC9aa+o/yHaNJy1ab42sW7snXUoUSfeNLy8f3Uy9mohdXa14GoyV4uedYs6kGfdmq9b9Z7rVi1Z3Bfdqse69YA28P1WL55U21fb9kO/DFmXzP7q0o7mUObo0+ikt3m6Ze9Rtzq7pWrJdPautEt2A0731dn+U/sD' \
			b'1PKGbHxgGvkSvduHqbyHUr316sa6dQhTdWlztpvpue2aNFtdkyy7GrJkcSPcyVfpHYfzEbX9m0u6u1jo55bxWRwjHw8J25BIlnyAK2/zpzxTdmUE3WY7i3rH3BdmLRtTjf7kySZ70pTf38F3c4ov5siGP15d7Kfs/Mdo8KEYPv2mwh8FNLyMKLhG9kghEptd' \
			b'2RZRcxQ/TPy5FeQ0sBtV8mhn5XH0YR/Jpv+M1sqsEpAn/9gwnvkpjYxCsubmZG3ys0M35o6rLeSQ2pbJPzbfr4pzYlinq+SyTXPJe9QGyevoa0s4GiH7htLNB8fkH03ibyV1Vfw8Et/7zyHVqwubfbaI2+Rl8lmipoqfH2rTTw694TYcf50YnFv85IGpa0d/' \
			b'Y5qE1apHQ2At/ybJQPacSL67B/3oqi3/JId9mcPbacVYJab1YYYuzNKBofJ//NJNPYUbRn9TNKueGJEUDESUwz1UNgtv906yXy/vWhVu2zrM0gjuT92pE/N54drtmEHu9X3oTVvdgUP+zcG8XuYpEPc+1HEuTJWGbOm4Z397LisdKmJNZ842a+B6ozp5+QWV' \
			b'4gHTakejnxtieZQzHdHFCBTKHpd28RjzwBzqYU1Xd61yQdgbqpitbuP8OHodIQp4OL3kWYrGZowDc6iHUZ95XAPzdA3y3kDjpqRoqtT1uXe+82ac9YSFTUZE0h+ZajbVoTnUw6iH/6CqaasHcrA5LY9MKV11aA71MBo+PKhSttUDOQjjyMYi/MY4MId6GA1F' \
			b'bqeUw7rBSTtDNy2qfUeOK3M6oh1WPQTZjOzZK7Rzh+KZ0ruVYjLVzY6o19LMcSmfKZ6Q1mjcsWfSstV+OEir3XNptdV+OEhrxlBjn43ffODFDIfp5/g/87Htn58kgsQPfLqBp/v33UHQM4Yqey1oW+29wwT6nc+a3LGgXbX3DoKeMc7Za0G31d47CJq/t8tr' \
			b'Rjr1N96Pvj1/6BES4TDe3qcVRD21tDZqeYjkwJ/4qvlTMnWLHjB/bGyCsqsSB8JuRMg1wMR9lbq61Qf6ZJ0NW5s1eJCTeoNajGq5a2Rutc6XaZVLq3pYKPmbENitI5WLadkBK7pYHQZdtlLzXJIw5uK8ufx/pcVBug=='

	_PARSER_TOP             = 'expr_commas'
	_PARSER_CONFLICT_REDUCE = {'BAR'}

	_VAR_TEX_XLAT = {
		r'\mathbb{R}'  : 'Reals',
		r'\mathbb{C}'  : 'Complexes',
		r'\mathbb{N}'  : 'Naturals',
		r'\mathbb{N}_0': 'Naturals0',
		r'\mathbb{Z}'  : 'Integers',
	}

	_UPARTIAL = '\u2202'
	_USUM     = '\u2211'
	_UINTG    = '\u222b'
	_LETTER   = fr'[a-zA-Z]'
	_LETTERU  = fr'[a-zA-Z_]'

	_TEXGREEK = '(?:' + '|'.join (reversed (sorted (f'\\\\{g}' for g in AST.Var.GREEK))) + ')'
	_TEXXLAT  = '(?:' + '|'.join (reversed (sorted (x.replace ('\\', '\\\\') for x in _VAR_TEX_XLAT))) + ')'
	_VARPY    = fr'(?:{_LETTER}(?:\w|\\_)*)'
	_VARTEX   = fr'(?:{_TEXGREEK}|{_TEXXLAT}|\\partial|(?:(?:\\overline|\\bar|\\widetilde|\\tilde)\s*)?\\infty)'
	_VARTEX1  = fr'(?:(\d)|({_LETTER})|({_VARTEX}))'
	_VARUNI   = fr'(?:{"|".join (AST.Var.UNI2PY)})'
	_VAR      = fr'(?:{_VARPY}|{_VARTEX}(?!{_LETTERU})|{_VARUNI})'

	_STR      = r'\'(?:\\.|[^\'])*\'|"(?:\\.|[^"])*["]'

	_FUNCPY   = f"(?:{'|'.join (reversed (sorted (AST.Func.PY - {AST.Func.NOREMAP, AST.Func.NOEVAL})))})"
	_FUNCTEX  = f"(?:{'|'.join (reversed (sorted (AST.Func.TEX)))})"

	TOKENS    = OrderedDict ([ # order matters
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})(?!{_LETTERU})|(\${_LETTERU}\w*)|\\operatorname\s*{{\s*(@|\\\%|\$?{_LETTER}(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!
		('SQRT',          r'sqrt\b|\\sqrt(?!{_LETTER})'),
		('LOG',           r'log\b|\\log(?!{_LETTER})'),
		('LN',            r'ln\b|\\ln(?!{_LETTER})'),
		('LIM',          fr'\\lim(?!{_LETTER})'),
		('SUM',          fr'\\sum(?:\s*\\limits)?(?!{_LETTER})|{_USUM}'),
		('INTG',         fr'\\int(?:\s*\\limits)?(?!{_LETTER})|{_UINTG}'),
		('LEFT',         fr'\\left(?!{_LETTERU})'),
		('RIGHT',        fr'\\right(?!{_LETTERU})'),
		('CDOT',         fr'\\cdot(?!{_LETTERU})'),
		('TO',           fr'\\to(?!{_LETTERU})'),
		('MAPSTO',       fr'\\mapsto(?!{_LETTERU})'),
		('BEG_MAT',       r'\\begin\s*{\s*matrix\s*}'),
		('END_MAT',       r'\\end\s*{\s*matrix\s*}'),
		('BEG_BMAT',      r'\\begin\s*{\s*bmatrix\s*}'),
		('END_BMAT',      r'\\end\s*{\s*bmatrix\s*}'),
		('BEG_VMAT',      r'\\begin\s*{\s*vmatrix\s*}'),
		('END_VMAT',      r'\\end\s*{\s*vmatrix\s*}'),
		('BEG_PMAT',      r'\\begin\s*{\s*pmatrix\s*}'),
		('END_PMAT',      r'\\end\s*{\s*pmatrix\s*}'),
		('BEG_CASES',     r'\\begin\s*{\s*cases\s*}'),
		('END_CASES',     r'\\end\s*{\s*cases\s*}'),
		('FRAC2',        fr'\\frac\s*{_VARTEX1}\s*{_VARTEX1}'),
		('FRAC1',        fr'\\frac\s*{_VARTEX1}'),
		('FRAC',          r'\\frac'),
		('IF',            r'if(?!{_LETTERU})'),
		('ELSE',          r'else(?!{_LETTERU})'),
		('NUM',           r'(?:(\d*\.\d+)|(\d+)\.?)([eE][+-]?\d+)?'),
		('VAR',          fr"(?:(?:(\\partial\s?|{_UPARTIAL})|(d))({_VAR})|({_VAR}))('*)"),
		('ATTR',         fr'\.(?:({_LETTERU}\w*)|\\operatorname\s*{{\s*({_LETTER}(?:\w|\\_)*)\s*}})'),
		('STR',          fr"({_STR})|\\text\s*{{\s*({_STR})\s*}}"),
		('SUB1',         fr'_{_VARTEX1}'),
		('SUB',           r'_'),
		('CARET1',       fr'\^{_VARTEX1}'),
		('CARET',         r'\^'),
		('DBLSTAR',       r'\*\*'),
		('PARENL',        r'\('),
		('PARENR',        r'\)'),
		('CURLYL',        r'{'),
		('CURLYR',        r'}'),
		('BRACKL',        r'\['),
		('BRACKR',        r'\]'),
		('BAR',           r'\|'),
		('PLUS',          r'\+'),
		('MINUS',         r'-'),
		('STAR',          r'\*'),
		('INEQ',         fr'==|!=|\\neq?|<=|\\le|<|\\lt|>=|\\ge|>|\\gt|{"|".join (AST.Eq.UNI2PY)}'),
		('EQ',            r'='),
		('DIVIDE',        r'/'),
		('EXCL',          r'!'),
		('AMP',           r'&'),
		('COLON',         r':'),
		('DBLSLASH',      r'\\\\'),
		('COMMA',         r','),
		('IGNORE_CURLY',  r'\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		('ignore',        r'\\,|\\:|\\?\s+|\\text\s*{\s*[^}]*\s*}'),
	])

	_VARPY_QUICK = fr'(?:{_LETTER})'
	_VAR_QUICK   = fr'(?:{_VARPY_QUICK}|{_VARTEX}|{_VARUNI})'

	TOKENS_QUICK = OrderedDict ([ # quick input mode different tokens
		('FUNC',         fr'(@|\%|{_FUNCPY})|\\({_FUNCTEX})|(\${_LETTERU}\w*)|\\operatorname\s*{{\s*(@|\\\%|{_LETTER}(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!
		('SQRT',          r'sqrt|\\sqrt'),
		('LOG',           r'log|\\log'),
		('LN',            r'ln|\\ln'),
		('LIM',          fr'\\lim'),
		('SUM',          fr'\\sum(?:\s*\\limits)?|{_USUM}'),
		('INTG',         fr'\\int(?:\s*\\limits)?|{_UINTG}'),
		('LEFT',         fr'\\left'),
		('RIGHT',        fr'\\right'),
		('CDOT',         fr'\\cdot'),
		('TO',           fr'\\to'),
		('MAPSTO',       fr'\\mapsto'),
		('IF',            r'if'),
		('ELSE',          r'else'),
		('VAR',          fr"(?:(?:(\\partial\s?|{_UPARTIAL})|(d))({_VAR_QUICK})|({_VAR_QUICK}))('*)"),
	])

	TOKENS_LONG  = OrderedDict () # initialized in __init__()

	def expr_commas_1      (self, expr_comma, COMMA):                              return expr_comma if expr_comma.is_comma else AST (',', (expr_comma,))
	def expr_commas_2      (self, expr_comma):                                     return expr_comma
	def expr_commas_3      (self):                                                 return AST (',', ())
	def expr_comma_1       (self, expr_comma, COMMA, expr):                        return AST.flatcat (',', expr_comma, expr)
	def expr_comma_2       (self, expr):                                           return expr

	def expr               (self, expr_eq):                                        return expr_eq

	def expr_eq_1          (self, expr_lambda1, EQ, expr_lambda2):                 return AST ('=', '=', expr_lambda1, expr_lambda2)
	def expr_eq_2          (self, expr_lambda):                                    return expr_lambda

	def expr_lambda_1      (self, expr_var, expr_commas, COLON, expr_eq):
		if expr_var.is_var_lambda:
			return _expr_lambda (expr_commas, expr_eq)
		else:
			raise SyntaxError ()

	def expr_lambda_2      (self, expr_mapsto):                                    return expr_mapsto

	def expr_mapsto_1      (self, expr_paren, MAPSTO, expr_eq):                    return _expr_lambda (expr_paren.strip (), expr_eq)
	def expr_mapsto_2      (self, expr_piece):                                     return expr_piece

	def expr_piece_1       (self, expr_ineq, IF, expr, ELSE, expr_lambda):
		return \
				AST ('piece', ((expr_ineq, expr),) + expr_lambda.pieces) \
				if expr_lambda.is_piece else \
				AST ('piece', ((expr_ineq, expr), (expr_lambda, True)))

	def expr_piece_2       (self, expr_ineq, IF, expr):                            return AST ('piece', ((expr_ineq, expr),))
	def expr_piece_3       (self, expr_ineq):                                      return expr_ineq

	def expr_ineq_2        (self, expr_add1, INEQ, expr_add2):                     return AST ('=', AST.Eq.ANY2PY.get (INEQ.text, INEQ.text), expr_add1, expr_add2)
	def expr_ineq_3        (self, expr_add):                                       return expr_add

	def expr_add_1         (self, expr_add, PLUS, expr_mul_exp):                   return AST.flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2         (self, expr_add, MINUS, expr_mul_exp):                  return AST.flatcat ('+', expr_add, expr_mul_exp.neg (stack = True))
	def expr_add_3         (self, expr_mul_exp):                                   return expr_mul_exp

	def expr_mul_exp_1     (self, expr_mul_exp, CDOT, expr_neg):                   return AST.flatcat ('*', expr_mul_exp, expr_neg)
	def expr_mul_exp_2     (self, expr_mul_exp, STAR, expr_neg):                   return AST.flatcat ('*', expr_mul_exp, expr_neg)
	def expr_mul_exp_3     (self, expr_neg):                                       return expr_neg

	def expr_neg_1         (self, MINUS, expr_neg):                                return expr_neg.neg (stack = True)
	def expr_neg_2         (self, expr_diff):                                      return expr_diff

	def expr_diff          (self, expr_div):                                       return _expr_diff (expr_div)

	def expr_div_1         (self, expr_div, DIVIDE, expr_mul_imp):                 return AST ('/', expr_div, expr_mul_imp)
	def expr_div_2         (self, expr_div, DIVIDE, MINUS, expr_mul_imp):          return AST ('/', expr_div, expr_mul_imp.neg (stack = True))
	def expr_div_3         (self, expr_mul_imp):                                   return expr_mul_imp

	def expr_mul_imp_1     (self, expr_mul_imp, expr_intg):                        return _expr_mul_imp (expr_mul_imp, expr_intg, self._USER_FUNCS)
	def expr_mul_imp_2     (self, expr_intg):                                      return expr_intg

	def expr_intg_1        (self, INTG, expr_sub, expr_super, expr_add):           return _expr_intg (expr_add, (expr_sub, expr_super))
	def expr_intg_2        (self, INTG, expr_add):                                 return _expr_intg (expr_add)
	def expr_intg_3        (self, expr_lim):                                       return expr_lim

	def expr_lim_1         (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                           return AST ('lim', expr_neg, expr_var, expr)
	def expr_lim_2         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, PLUS, CURLYR, expr_neg):   return AST ('lim', expr_neg, expr_var, expr, '+')
	def expr_lim_3         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, MINUS, CURLYR, expr_neg):  return AST ('lim', expr_neg, expr_var, expr, '-')
	def expr_lim_6         (self, expr_sum):                                                                         return expr_sum

	def expr_sum_1         (self, SUM, SUB, CURLYL, expr_var, EQ, expr, CURLYR, expr_super, expr_neg):               return AST ('sum', expr_neg, expr_var, expr, expr_super)
	def expr_sum_2         (self, expr_func):                                                                        return expr_func

	def expr_func_1        (self, SQRT, expr_neg_func):                            return _expr_func (1, 'sqrt', expr_neg_func)
	def expr_func_2        (self, SQRT, BRACKL, expr, BRACKR, expr_neg_func):      return _expr_func (1, 'sqrt', expr_neg_func, expr)
	def expr_func_3        (self, LN, expr_neg_func):                              return _expr_func (1, 'log', expr_neg_func)
	def expr_func_4        (self, LOG, expr_neg_func):                             return _expr_func (1, 'log', expr_neg_func)
	def expr_func_5        (self, LOG, expr_sub, expr_neg_func):                   return _expr_func (1, 'log', expr_neg_func, expr_sub)
	def expr_func_6        (self, FUNC, expr_neg_func):                            return _expr_func_func (FUNC, expr_neg_func)
	def expr_func_7        (self, FUNC, expr_super, expr_neg_func):
		func = _FUNC_name (FUNC)

		return \
				AST ('^', _expr_func_func (FUNC, expr_neg_func), expr_super) \
				if expr_super.remove_curlys () != AST.NegOne or not AST ('func', func, ()).is_trigh_func_noninv else \
				_expr_func_func (f'a{func}', expr_neg_func)

	def expr_func_8        (self, expr_pow):                                       return expr_pow

	def expr_pow_1         (self, expr_pow, expr_super):                           return AST ('^', expr_pow, expr_super)
	def expr_pow_2         (self, expr_fact):                                      return expr_fact

	def expr_fact_1        (self, expr_fact, EXCL):                                return AST ('!', expr_fact)
	def expr_fact_2        (self, expr_attr):                                      return expr_attr

	def expr_attr_1        (self, expr_attr, ATTR):                                return AST ('.', expr_attr, ATTR.grp [0] or ATTR.grp [1])
	def expr_attr_2        (self, expr_abs):                                       return expr_abs

	def expr_abs_1         (self, LEFT, BAR1, expr_commas, RIGHT, BAR2):           return AST ('|', expr_commas)
	def expr_abs_2         (self, BAR1, expr_commas, BAR2):                        return AST ('|', expr_commas)
	def expr_abs_3         (self, expr_paren):                                     return expr_paren

	def expr_paren_1       (self, LEFT, PARENL, expr_commas, RIGHT, PARENR):       return AST ('(', expr_commas)
	def expr_paren_2       (self, PARENL, expr_commas, PARENR):                    return AST ('(', expr_commas)
	def expr_paren_3       (self, IGNORE_CURLY, CURLYL, expr, CURLYR):             return AST ('{', expr)
	def expr_paren_4       (self, expr_frac):                                      return expr_frac

	def expr_frac_1        (self, FRAC, expr_cases1, expr_cases2):                 return AST ('/', expr_cases1.remove_curlys (), expr_cases2.remove_curlys ())
	def expr_frac_2        (self, FRAC1, expr_cases):                              return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_cases.remove_curlys ())
	def expr_frac_3        (self, FRAC2):                                          return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3))
	def expr_frac_4        (self, expr_cases):                                     return expr_cases

	def expr_cases_1       (self, BEG_CASES, expr_casess, END_CASES):              return AST ('piece', expr_casess) # translate this on the fly?
	def expr_cases_2       (self, expr_mat):                                       return expr_mat
	def expr_casess_1      (self, expr_casessp, DBLSLASH):                         return expr_casessp
	def expr_casess_2      (self, expr_casessp):                                   return expr_casessp
	def expr_casessp_1     (self, expr_casessp, DBLSLASH, expr_casessc):           return expr_casessp + (expr_casessc,)
	def expr_casessp_2     (self, expr_casessc):                                   return (expr_casessc,)
	def expr_casessc_1     (self, expr1, AMP, expr2):                              return (expr1, expr2)
	def expr_casessc_2     (self, expr, AMP):                                      return (expr, True)

	def expr_mat_1         (self, LEFT, BRACKL, BEG_MAT, expr_mat_rows, END_MAT, RIGHT, BRACKR):  return _expr_mat (expr_mat_rows) # translate these on the fly?
	def expr_mat_2         (self, BEG_MAT, expr_mat_rows, END_MAT):                               return _expr_mat (expr_mat_rows)
	def expr_mat_3         (self, BEG_BMAT, expr_mat_rows, END_BMAT):                             return _expr_mat (expr_mat_rows)
	def expr_mat_4         (self, BEG_VMAT, expr_mat_rows, END_VMAT):                             return _expr_mat (expr_mat_rows)
	def expr_mat_5         (self, BEG_PMAT, expr_mat_rows, END_PMAT):                             return _expr_mat (expr_mat_rows)
	def expr_mat_6         (self, expr_curly):                                                    return expr_curly
	def expr_mat_rows_1    (self, expr_mat_row, DBLSLASH):                         return expr_mat_row
	def expr_mat_rows_2    (self, expr_mat_row):                                   return expr_mat_row
	def expr_mat_rows_3    (self):                                                 return ()
	def expr_mat_row_1     (self, expr_mat_row, DBLSLASH, expr_mat_col):           return expr_mat_row + (expr_mat_col,)
	def expr_mat_row_2     (self, expr_mat_col):                                   return (expr_mat_col,)
	def expr_mat_col_1     (self, expr_mat_col, AMP, expr):                        return expr_mat_col + (expr,)
	def expr_mat_col_2     (self, expr):                                           return (expr,)

	def expr_curly_1       (self, CURLYL, expr_commas, CURLYR):                    return _expr_curly (expr_commas)
	def expr_curly_2       (self, expr_bracket):                                   return expr_bracket

	def expr_bracket_1     (self, LEFT, BRACKL, expr_commas, RIGHT, BRACKR):       return AST ('[', expr_commas.commas if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_2     (self, BRACKL, expr_commas, BRACKR):                    return AST ('[', expr_commas.commas if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_3     (self, expr_term):                                      return expr_term

	def expr_term_1        (self, expr_num):                                       return expr_num
	def expr_term_2        (self, expr_var):                                       return expr_var
	def expr_term_3        (self, STR):                                            return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1]))
	def expr_term_4        (self, SUB):                                            return AST ('@', '_') # for last expression variable

	def expr_num           (self, NUM):                                            return AST ('#', NUM.text) if NUM.grp [0] or NUM.grp [2] else AST ('#', NUM.grp [1])
	def expr_var           (self, VAR):
		var = \
				'partial' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_')) \
				if VAR.grp [0] else \
				'd' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_')) \
				if VAR.grp [1] else \
				self._VAR_TEX_XLAT [VAR.grp [3]] \
				if VAR.grp [3] in self._VAR_TEX_XLAT else \
				AST.Var.ANY2PY.get (VAR.grp [3].replace (' ', ''), VAR.grp [3].replace ('\\_', '_'))

		return AST ('@', var + '_prime' * len (VAR.grp [4]))

	def expr_sub_1         (self, SUB, expr_frac):                                 return expr_frac
	def expr_sub_2         (self, SUB1):                                           return _ast_from_tok_digit_or_var (SUB1)

	def expr_super_1       (self, DBLSTAR, expr_neg_func):                         return expr_neg_func
	def expr_super_3       (self, CARET, expr_frac):                               return expr_frac
	def expr_super_4       (self, CARET1):                                         return _ast_from_tok_digit_or_var (CARET1)

	def expr_neg_func_1    (self, MINUS, expr_neg_func):                           return expr_neg_func.neg (stack = True)
	def expr_neg_func_2    (self, expr_func):                                      return expr_func

	def caret_or_dblstar_1 (self, DBLSTAR):                                        return '**'
	def caret_or_dblstar_2 (self, CARET):                                          return '^'

	#...............................................................................................
	_AUTOCOMPLETE_SUBSTITUTE = { # autocomplete means autocomplete AST tree so it can be rendered, not necessarily expression
		'CARET1'             : 'CARET',
		'SUB1'               : 'SUB',
		'FRAC2'              : 'FRAC',
		'FRAC1'              : 'FRAC',
		'expr_super'         : 'CARET',
		'caret_or_doublestar': 'CARET',
	}

	_AUTOCOMPLETE_CONTINUE = {
		'RIGHT' : ' \\right',
		'COMMA' : ',',
		'PARENL': '(',
		'PARENR': ')',
		'CURLYR': '}',
		'BRACKR': ']',
		'BAR'   : '|',
	}

	def _insert_symbol (self, sym, tokinc = 0):
		tokidx       = self.tokidx
		self.tokidx += tokinc

		for sym in ((sym,) if isinstance (sym, str) else sym):
			if sym in self.TOKENS:
				self.tokens.insert (tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, sym), '', self.tok.pos))

				if self.autocompleting:
					if sym in self._AUTOCOMPLETE_CONTINUE:
						self.autocomplete.append (self._AUTOCOMPLETE_CONTINUE [sym])
					else:
						self.autocompleting = False

			else:
				self.tokens.insert (tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, 'VAR'), '', self.tok.pos, ('', '', '', '', '')))
				self._mark_error ()

			tokidx += 1

		return True # for convenience

	def _mark_error (self, sym_ins = None, tokinc = 0, at = None):
		self.autocompleting = False

		if self.erridx is None:
			self.erridx = self.tokens [self.tokidx].pos if at is None else at

		if sym_ins is not None:
			return self._insert_symbol (sym_ins, tokinc)

	def _parse_autocomplete_expr_commas (self, rule, pos):
		idx = -pos + (self.stack [-pos].sym == 'LEFT')

		if self.stack [idx].sym != 'CURLYL':
			if self.tokens [self.tokidx - 1] == 'COMMA':
				self._mark_error ()

			if self.stack [idx - 1].sym == 'LEFT':
				return self._insert_symbol ('RIGHT')

			return self._insert_symbol ('PARENR' if self.stack [idx].sym == 'PARENL' else 'BRACKR')

		# vector or matrix potentially being entered
		if self.stack [idx - 1].sym == 'CURLYL':
			if self.stack [-1].red.is_null_var:
				return self._mark_error (('CURLYR', 'CURLYR'))
			elif not self.stack [-1].red.is_comma:
				return self._insert_symbol (('COMMA', 'CURLYR', 'COMMA', 'CURLYR'), 1)
			elif len (self.stack [-1].red.commas) == 1 or self.tokens [self.tokidx - 1] != 'COMMA':
				return self._insert_symbol (('CURLYR', 'COMMA', 'CURLYR'))
			else:
				return self._mark_error (('CURLYR', 'CURLYR'))

		if self.stack [-3].sym != 'COMMA' or self.stack [-4].sym != 'expr_comma' or self.stack [-5].sym != 'CURLYL':
			if self.stack [-1].red.is_vec:
				return self._insert_symbol (('COMMA', 'CURLYR'), 1)
			elif self.stack [-1].red.is_comma:
				if len (self.stack [-1].red.commas) == 1 or self.tokens [self.tokidx - 1] != 'COMMA':
					return self._insert_symbol ('CURLYR')
				else:
					return self._mark_error ('CURLYR')

		else:
			cols = \
					len (self.stack [-4].red.vec)             if self.stack [-4].red.is_vec else \
					len (self.stack [-4].red.commas [0].vec)  if self.stack [-4].red.is_comma and self.stack [-4].red.commas [0].is_vec else \
					None

			if cols is not None:
				vec             = self.stack [-1].red.commas if self.stack [-1].red.is_comma else (self.stack [-1].red,)
				self.stack [-1] = lalr1.State (self.stack [-1].idx, self.stack [-1].sym, AST (',', vec + (AST.VarNull,) * (cols - len (vec))))

				return self._mark_error (('CURLYR', 'CURLYR')) if len (vec) != cols else self._insert_symbol (('CURLYR', 'CURLYR'))

		return self._insert_symbol ('CURLYR')

	def _parse_autocomplete_expr_intg (self):
		s               = self.stack [-1]
		self.stack [-1] = lalr1.State (s.idx, s.sym, AST ('*', (s.red, AST.VarNull)))
		expr_vars       = set ()

		if self.autocompleting:
			stack = [s [2]]

			while stack:
				ast = stack.pop ()

				if ast.is_var:
					if not (ast.is_differential or ast.is_part_any):
						expr_vars.add (ast.var)
				else:
					stack.extend (filter (lambda a: isinstance (a, tuple), ast))

		expr_vars = expr_vars - {'_'} - {ast.var for ast in AST.CONSTS}

		if len (expr_vars) == 1:
			self.autocomplete.append (f' d{expr_vars.pop ()}')
		else:
			self._mark_error ()

		return True

	def parse_getextrastate (self):
		return (self.autocomplete [:], self.autocompleting, self.erridx)

	def parse_setextrastate (self, state):
		self.autocomplete, self.autocompleting, self.erridx = state

	def parse_error (self): # add tokens to continue parsing for autocomplete if syntax allows
		if isinstance (self.rederr, lalr1.Incomplete):
			self.parse_results.append ((self.rederr.red, self.tok.pos, []))

			return False

		if self.tok != '$end':
			self.parse_results.append ((None, self.tok.pos, []))

			return False

		if self.tokidx and self.tokens [self.tokidx - 1] == 'LEFT':
			for irule, pos in self.strules [self.stidx]:
				if self.rules [irule] [1] [pos] == 'PARENL':
					break
			else:
				raise RuntimeError ('could not find left parenthesis rule')

		else:
			irule, pos = self.strules [self.stidx] [0]

		rule = self.rules [irule]

		if pos == 1 and rule == ('expr_func', ('FUNC', 'expr_neg_func')):
			return self._insert_symbol (('PARENL', 'PARENR'))

		if pos and rule [1] [pos - 1] == 'expr_commas':
			return self._parse_autocomplete_expr_commas (rule, pos)

		if pos >= len (rule [1]): # end of rule
			if rule [0] == 'expr_intg': # TODO: Fix this!
				return self._parse_autocomplete_expr_intg ()

			return False

		return self._insert_symbol (rule [1] [pos])

	def parse_success (self, red):
		self.parse_results.append ((red, self.erridx, self.autocomplete))

		return True # continue parsing if conflict branches remain to find best resolution

	def parse (self, text):
		if not text.strip ():
			return (AST.VarNull, 0, [])

		self.parse_results  = [] # [(reduction, erridx, autocomplete), ...]
		self.autocomplete   = []
		self.autocompleting = True
		self.erridx         = None

		lalr1.Parser.parse (self, text)

		if not self.parse_results:
			return (None, 0, [])

		rated = sorted ((r is None, -e if e is not None else float ('-inf'), len (a), i, (r, e, a)) \
				for i, (r, e, a) in enumerate (self.parse_results))

		if os.environ.get ('SYMPAD_DEBUG'):
			rated = list (rated)

			print (file = sys.stderr)

			for res in rated [:32]:
				res = res [-1]
				res = (res [0].remove_curlys (),) + res [1:] if isinstance (res [0], AST) else res

				print ('parse:', res, file = sys.stderr)

			if len (rated) > 32:
				print (f'... total {len (rated)}', file = sys.stderr)

			print (file = sys.stderr)

		res = next (iter (rated)) [-1]

		return (res [0].remove_curlys (),) + res [1:] if isinstance (res [0], AST) else res

class sparser: # for single script
	Parser = Parser

if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: ## DEBUG!
	p = Parser ()
	a = p.parse (r'Piecewise ((1,True))') [0]
	# a = sym.ast2spt (a)
	print (a)
#!/usr/bin/env python
# python 3.6+

import getopt
import io
import json
import os
import re
import subprocess
import sys
import time
import threading
import traceback
import webbrowser

from urllib.parse import parse_qs
from socketserver import ThreadingMixIn
from http.server import HTTPServer, SimpleHTTPRequestHandler

_VERSION                  = 'v0.5.0'


_SYMPAD_PATH              = os.path.dirname (sys.argv [0])
_SYMPAD_FIRST_RUN         = os.environ.get ('SYMPAD_FIRST_RUN')
_SYMPAD_CHILD             = os.environ.get ('SYMPAD_CHILD')

_DEFAULT_ADDRESS          = ('localhost', 8000)
_STATIC_FILES             = {'/style.css': 'css', '/script.js': 'javascript', '/index.html': 'html', '/help.html': 'html'}
_DISPLAYSTYLE             = [1]

_HELP = f"""
usage: {os.path.basename (sys.argv [0])} [--help | -h] [--debug | -d] [--nobrowser | -n] [--sympyEI | -E] [--quick | -q] [--ugly | -u] [host:port]
"""

if _SYMPAD_CHILD: # sympy slow to import so don't do it for watcher process as is unnecessary there
	sys.path.insert (0, '') # allow importing from current directory first (for SymPy development version)


	_VAR_LAST   = '_'
	_START_VARS = {
		'beta' : AST ('lamb', ('func', '$beta', (('@', 'x'), ('@', 'y'))), (('@', 'x'), ('@', 'y'))),
		'gamma': AST ('lamb', ('func', '$gamma', (('@', 'z'),)), (('@', 'z'),)),
		'Gamma': AST ('lamb', ('func', '$gamma', (('@', 'z'),)), (('@', 'z'),)),
		'zeta' : AST ('lamb', ('func', '$zeta', (('@', 'z'),)), (('@', 'z'),)),
	}

	_sys_stdout = sys.stdout
	_parser     = sparser.Parser ()

	_vars       = {_VAR_LAST: AST.Zero} # This is individual session STATE! Threading can corrupt this! It is GLOBAL to survive multiple Handlers.
	_history    = [] # persistent history across browser closing

#...............................................................................................
# class ThreadingHTTPServer (ThreadingMixIn, HTTPServer):
# 	pass

class RealityRedefinitionError (NameError):	pass
class CircularReferenceError (RecursionError): pass
class AE35UnitError (Exception): pass

def _ast_remap (ast, map_):
	if not isinstance (ast, AST) or (ast.is_func and ast.func == AST.Func.NOREMAP): # non-AST or stop remap
		return ast

	if ast.is_var and ast.var in map_: # variable
		ast = map_ [ast.var]

		return AST ('func', AST.Func.NOEVAL, (ast,)) if ast.is_lamb else _ast_remap (ast, map_)

	if ast.is_func and ast.func in map_: # user function
		lamb = map_ [ast.func]

		if lamb.is_lamb:
			if len (ast.args) != len (lamb.vars):
				raise TypeError (f"lambda function '{ast.func}()' takes {len (lamb.vars)} argument(s)")

			ast = _ast_remap (lamb.lamb, dict (zip ((v.var for v in lamb.vars), ast.args)))

	if ast.is_lamb: # do not remap lambda owned vars within lambda, they belong to the lambda
		lvars = {v.var for v in ast.vars}
		map_  = {v: a for v, a in filter (lambda va: va [0] not in lvars, map_.items ())}

		return AST (*(_ast_remap (a, map_) if a not in ast.vars else a for a in ast))

	return AST (*(_ast_remap (a, map_) for a in ast))

def _ast_prepare_ass (ast): # check and prepare for simple or tuple assignment
	vars = None

	if ast.is_ass:
		if ast.lhs.is_var: # simple assignment?
			ast, vars = ast.rhs, [ast.lhs.var]

	elif ast.is_comma: # tuple assignment? ('x, y = y, x' comes from parser as ('x', 'y = y', 'x')) so restructure
		lhss = []
		itr  = iter (ast.commas)

		for c in itr:
			if c.is_var:
				lhss.append (c.var)
			elif not c.is_ass or not c.lhs.is_var:
				break

			else:
				t    = (c.rhs,) + tuple (itr)
				ast  = t [0] if len (t) == 1 else AST (',', t)
				vars = lhss + [c.lhs.var]

	if vars:
		for var in vars: # trying to change a fundemental law of the universe?
			if AST ('@', var) in AST.CONSTS:
				raise RealityRedefinitionError ('The only thing that is constant is change - Heraclitus, except for constants, they never change - Me.')

	return _ast_remap (ast, _vars), vars

def _ast_execute_ass (ast, vars): # execute assignment if it was detected
	def _set_vars (vars):
		try: # check for circular references
			_ast_remap (AST (',', tuple (('@', v) for v in vars)), {**_vars, **vars})
		except RecursionError:
			raise CircularReferenceError ("I'm sorry, Dave. I'm afraid I can't do that.") from None

		_vars.update (vars)

	if not vars: # no assignment
		_vars [_VAR_LAST] = ast

		return [ast]

	if len (vars) == 1: # simple assignment
		_set_vars ({vars [0]: ast})

		asts = [AST ('=', '=', ('@', vars [0]), ast)]

	else: # tuple assignment
		ast  = ast.strip_paren ()
		asts = ast.commas if ast.is_comma else tuple (sym.spt2ast (a) for a in sym.ast2spt (ast))

		if len (vars) < len (asts):
			raise ValueError (f'too many values to unpack (expected {len (vars)})')
		if len (vars) > len (asts):
			raise ValueError (f'not enough values to unpack (expected {len (vars)}, got {len (asts)})')

		_set_vars (dict (zip (vars, asts)))

		asts = [AST ('=', '=', ('@', vars [i]), asts [i]) for i in range (len (vars))]

	user_funcs = {va [0] for va in filter (lambda va: va [1].is_lamb, _vars.items ())}

	sym.set_user_funcs (user_funcs)
	_parser.set_user_funcs (user_funcs)

	return asts

def _admin_vars (ast):
	asts = []

	for v, e in sorted (_vars.items ()):
		if v != _VAR_LAST:
			if not e.is_lamb:
				asts.append (AST ('=', '=', ('@', v), e))

	if not asts:
		return 'No variables defined.'

	return asts

def _admin_funcs (ast):
	asts = []

	for v, e in sorted (_vars.items ()):
		if v != _VAR_LAST:
			if e.is_lamb:
				asts.append (AST ('=', '=', ('@', v), e))

	if not asts:
		return 'No functions defined.'

	return asts

def _admin_del (ast):
	var = ast.args [0] if ast.args else AST.VarNull

	try:
		ast = _vars [var.var]

		del _vars [var.var]

	except KeyError:
		raise AE35UnitError (f'Variable {sym.ast2nat (var)!r} is not defined, it can only be attributable to human error.')

	return f'{"Function" if ast.is_lamb else "Variable"} {sym.ast2nat (var)!r} deleted.'

def _admin_delvars (ast):
	for v, e in list (_vars.items ()):
		if not e.is_lamb:# and v != _VAR_LAST:
			del _vars [v]

	return 'All variables deleted.'

def _admin_delall (ast):
	last_var = _vars [_VAR_LAST]

	_vars.clear ()

	_vars [_VAR_LAST] = last_var

	return 'All assignments deleted.'

def _admin_sympyEI (ast):
	sast.sympyEI (bool (sym.ast2spt (ast.args [0])) if ast.args else True)

	if AST.E.var in _vars:
		del _vars [AST.E.var]

	if AST.I.var in _vars:
		del _vars [AST.I.var]

	return f'Constant representation set to {AST.E.var!r} and {AST.I.var!r}.'

def _admin_quick (ast):
	yes = bool (sym.ast2spt (ast.args [0])) if ast.args else True

	_parser.set_quick (yes)

	return f'Quick mode is {"on" if yes else "off"}.'

#...............................................................................................
class Handler (SimpleHTTPRequestHandler):
	def do_GET (self):
		if self.path == '/':
			self.path = '/index.html'

		fnm = os.path.join (_SYMPAD_PATH, self.path.lstrip ('/'))

		if self.path != '/env.js' and (self.path not in _STATIC_FILES or (not _RUNNING_AS_SINGLE_SCRIPT and not os.path.isfile (fnm))):
			self.send_error (404, f'Invalid path {self.path!r}')

		else:
			self.send_response (200)

			if self.path == '/env.js':
				content = 'text/javascript'
				data    = f'History = {_history}\nHistIdx = {len (_history)}\nVersion = {_VERSION!r}\nDisplayStyle = {_DISPLAYSTYLE [0]}'.encode ('utf8')

				self.send_header ('Cache-Control', 'no-store')

			else:
				content = _STATIC_FILES [self.path]

				if _RUNNING_AS_SINGLE_SCRIPT:
					data = _FILES [self.path [1:]]
				else:
					data = open (fnm, 'rb').read ()

			self.send_header ('Content-type', f'text/{content}')
			self.end_headers ()
			self.wfile.write (data)

	def do_POST (self):
		request = parse_qs (self.rfile.read (int (self.headers ['Content-Length'])).decode ('utf8'), keep_blank_values = True)

		for key, val in list (request.items ()):
			if isinstance (val, list) and len (val) == 1:
				request [key] = val [0]

		if request ['mode'] == 'validate':
			response = self.validate (request)
		else: # request ['mode'] == 'evaluate':
			response = self.evaluate (request)

		response ['mode'] = request ['mode']
		response ['idx']  = request ['idx']
		response ['text'] = request ['text']

		self.send_response (200)
		self.send_header ('Content-type', 'application/json')
		self.send_header ('Cache-Control', 'no-store')
		self.end_headers ()
		self.wfile.write (json.dumps (response).encode ('utf8'))
		# self.wfile.write (json.dumps ({**request, **response}).encode ('utf8'))

	def validate (self, request):
		ast, erridx, autocomplete = _parser.parse (request ['text'])
		tex = nat = py            = None

		if ast is not None:
			ast = _ast_remap (ast, {_VAR_LAST: _vars [_VAR_LAST]}) # just remap last evaluated _
			tex = sym.ast2tex (ast)
			nat = sym.ast2nat (ast)
			py  = sym.ast2py (ast)

			if os.environ.get ('SYMPAD_DEBUG'):
				print ('ast:', ast, file = sys.stderr)
				print ('tex:', tex, file = sys.stderr)
				print ('nat:', nat, file = sys.stderr)
				print ('py: ', py, file = sys.stderr)
				print (file = sys.stderr)

		return {
			'tex'         : tex,
			'nat'         : nat,
			'py'          : py,
			'erridx'      : erridx,
			'autocomplete': autocomplete,
		}

	def evaluate (self, request):
		try:
			_history.append (request ['text'])

			sys.stdout = io.StringIO ()
			ast, _, _  = _parser.parse (request ['text'])

			if ast.is_func and ast.func in AST.Func.ADMIN: # special admin function?
				asts = globals () [f'_admin_{ast.func}'] (ast)

				if isinstance (asts, str):
					return {'msg': [asts]}

			else: # not admin function, normal evaluation
				ast, vars = _ast_prepare_ass (ast)

				sym.set_precision (ast)

				spt = sym.ast2spt (ast)
				ast = sym.spt2ast (spt)

				if os.environ.get ('SYMPAD_DEBUG'):
					import sympy as sp

					print ('spt:        ', repr (spt), file = sys.stderr)
					print ('spt type:   ', type (spt), file = sys.stderr)
					print ('sympy latex:', sp.latex (spt), file = sys.stderr)
					print ('ast:        ', ast, file = sys.stderr)
					print (file = sys.stderr)

				asts = _ast_execute_ass (ast, vars)

			response = {}

			if asts and asts [0] is not AST.None_:
				response.update ({'math': [{
					'tex': sym.ast2tex (ast),
					'nat': sym.ast2nat (ast),
					'py' : sym.ast2py (ast),
				} for ast in asts]})

			if sys.stdout.tell ():
				sys.stdout.seek (0)

				response ['msg'] = sys.stdout.read ().strip ().split ('\n')

			return response

		except Exception:
			return {'err': ''.join (traceback.format_exception (*sys.exc_info ())).strip ().split ('\n')}

		finally:
			sys.stdout = _sys_stdout

#...............................................................................................
_month_name = (None, 'Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun', 'Jul', 'Aug', 'Sep', 'Oct', 'Nov', 'Dec')

if __name__ == '__main__':
	try:
		opts, argv = getopt.getopt (sys.argv [1:], 'hdnEqu', ['help', 'debug', 'nobrowser', 'sympyEI', 'quick', 'ugly'])

		if ('--help', '') in opts or ('-h', '') in opts:
			print (_HELP.strip ())
			sys.exit (0)

		if ('--debug', '') in opts or ('-d', '') in opts:
			os.environ ['SYMPAD_DEBUG'] = '1'

		if not _SYMPAD_CHILD: # watcher parent
			args      = [sys.executable] + sys.argv
			first_run = '1'

			while 1:
				ret       = subprocess.run (args, env = {**os.environ, 'SYMPAD_CHILD': '1', 'SYMPAD_FIRST_RUN': first_run})
				first_run = ''

				if ret.returncode != 0 and not os.environ.get ('SYMPAD_DEBUG'):
					sys.exit (0)

		# child starts here
		if ('--sympyEI', '') in opts or ('-E', '') in opts:
			sast.sympyEI ()

		if ('--quick', '') in opts or ('-q', '') in opts:
			_parser.set_quick ()

		if ('--ugly', '') in opts or ('-u', '') in opts:
			_DISPLAYSTYLE [0] = 0

		_vars.update (_START_VARS)
		sym.set_user_funcs (set (_START_VARS))
		_parser.set_user_funcs (set (_START_VARS))

		if not argv:
			host, port = _DEFAULT_ADDRESS
		else:
			host, port = (re.split (r'(?<=\]):' if argv [0].startswith ('[') else ':', argv [0]) + [_DEFAULT_ADDRESS [1]]) [:2]
			host, port = host.strip ('[]'), int (port)

		fnms    = ('sympad.py',) if _RUNNING_AS_SINGLE_SCRIPT else ('lalr1.py', 'xlat.py', 'sym.py', 'sparser.py', 'server.py')
		watch   = [os.path.join (_SYMPAD_PATH, fnm) for fnm in fnms]
		tstamps = [os.stat (fnm).st_mtime for fnm in watch]
		httpd   = HTTPServer ((host, port), Handler) # ThreadingHTTPServer ((host, port), Handler)
		thread  = threading.Thread (target = httpd.serve_forever, daemon = True)

		thread.start ()

		def log_message (msg):
			y, m, d, hh, mm, ss, _, _, _ = time.localtime (time.time ())

			sys.stderr.write (f'{httpd.server_address [0]} - - ' \
					f'[{"%02d/%3s/%04d %02d:%02d:%02d" % (d, _month_name [m], y, hh, mm, ss)}] {msg}\n')

		if _SYMPAD_FIRST_RUN:
			print ('Sympad server running. If a browser window does not automatically open to the address below then try navigating to that URL manually.\n')

		log_message (f'Serving at http://{httpd.server_address [0]}:{httpd.server_address [1]}/')

		if os.environ.get ('SYMPAD_FIRST_RUN') and ('--nobrowser', '') not in opts and ('-n', '') not in opts:
			webbrowser.open (f'http://{httpd.server_address [0] if httpd.server_address [0] != "0.0.0.0" else "127.0.0.1"}:{httpd.server_address [1]}')

		while 1:
			time.sleep (0.5)

			if [os.stat (fnm).st_mtime for fnm in watch] != tstamps:
				log_message ('Files changed, restarting...')
				sys.exit (0)

	except OSError as e:
		if e.errno != 98:
			raise

		print (f'Port {port} seems to be in use, try specifying different port as a command line parameter, e.g. localhost:8001')

	except KeyboardInterrupt:
		sys.exit (0)

	sys.exit (-1)
