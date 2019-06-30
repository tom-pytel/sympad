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

r"""// TODO: Warning messages on evaluate when SymPy object not understood.
// TODO: Move last evaluated expression '_' substitution here from the server side.
// TODO: Arrow keys in Edge?
// TODO: Change how error, auto and good text are displayed?

var URL              = '/';
var MJQueue          = null;
var MarginTop        = Infinity;
var PreventFocusOut  = true;

var History          = [];
var HistIdx          = 0;
var LogIdx           = 0;
var UniqueID         = 1;

var Validations      = [undefined];
var Evaluations      = [undefined];
var ErrorIdx         = null;
var Autocomplete     = [];

var LastClickTime    = 0;
var NumClicks        = 0;

var GreetingFadedOut = false;

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
	let margin = Math.max (BodyMarginTop, Math.floor (window.innerHeight - $('body').height () - BodyMarginBottom + 3)); // +3 is fudge factor

	if (margin < MarginTop) {
		MarginTop = margin
		$('body').css ({'margin-top': margin});
	}
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

	var TEX        = MathJax.InputJax.TeX;
	var PREFILTER  = TEX.prefilterMath;

	TEX.Augment ({
		prefilterMath: function (tex, displaymode, script) {
			return PREFILTER.call (TEX, '\\displaystyle{' + tex + '}', displaymode, script);
		}
	});
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
function copyToClipboard (e, val_or_eval, idx) {
	let t = performance.now ();

	if ((t - LastClickTime) > 500) {
		NumClicks = 1;
	} else{
		NumClicks += 1;
	}

	LastClickTime = t;
	let resp      = (val_or_eval ? Evaluations : Validations) [idx];

	writeToClipboard (NumClicks == 1 ? resp.simple : NumClicks == 2 ? resp.py : resp.tex);

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
			return; // ignore out of order responses
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
				}
			}]);

			reprioritizeMJQueue ();
		}

		updateOverlay (JQInput.val (), resp.erridx, resp.autocomplete);

	} else { // resp.mode == 'evaluate'
		Evaluations [resp.idx] = resp;

		let eLogEval = document.getElementById ('LogEval' + resp.idx);

		if (resp.err !== undefined) {
			eLogEval.removeChild (document.getElementById ('LogEvalWait' + resp.idx));

			if (resp.err.length > 1) {
				let idLogErrorHidden = 'LogErrorHidden' + resp.idx;
				$(eLogEval).append (`<div id="${idLogErrorHidden}" style="display: none"></div>`);
				var eLogErrorHidden  = document.getElementById (idLogErrorHidden);

				for (let i = 0; i < resp.err.length - 1; i ++) {
					$(eLogErrorHidden).append (`<div class="LogError">${resp.err [i]}</div>`);
				}
			}

			let idLogErrorTriangle = 'LogErrorTriangle' + resp.idx;
			$(eLogEval).append (`<div class="LogError">${resp.err [resp.err.length - 1]}</div><div class="LogErrorTriange" id="LogErrorTriangle${resp.idx}">\u25b7</div>`);
			var eLogErrorTriangle  = document.getElementById (idLogErrorTriangle);

			$(eLogEval).click (function () {
				if (eLogErrorHidden.style.display === 'none') {
					eLogErrorHidden.style.display = 'block';
					eLogErrorTriangle.innerText   = '\u25bd'; // '\u25bc'; // '-'; // '\u25bc';
				} else {
					eLogErrorHidden.style.display = 'none';
					eLogErrorTriangle.innerText   = '\u25b7'; // '\u25e2'; // '+'; // '\u25b6';
				}

				logResize ();
			});

			logResize ();
			scrollToEnd ();

		} else { // no error
			let idLogEvalMath = 'LogEvalMath' + resp.idx;
			$(eLogEval).append (`<span id="${idLogEvalMath}" style="visibility: hidden" onclick="copyToClipboard (this, 1, ${resp.idx})">$${resp.tex}$</span>`);
			let eLogEvalMath  = document.getElementById (idLogEvalMath);

			MJQueue.Push (['Typeset', MathJax.Hub, eLogEvalMath, function () {
				eLogEval.removeChild (document.getElementById ('LogEvalWait' + resp.idx));

				eLogEvalMath.style.visibility = '';

				logResize ();
				scrollToEnd ();
			}]);

			reprioritizeMJQueue ();
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

			if (Autocomplete [0] === '\\left' || Autocomplete [0] === '\\right') {
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
		<h5>v0.2</h5>
		<br><br>
		Type '<b>help</b>' at any time for more information.
		<br>
		- or -
		<br>
		Type or click any of the following to get started:
	</div>
	<br><br>
	<a class="GreetingA" href="javascript:inputting ('? sqrt 2', true)">? sqrt 2</a>
	<a class="GreetingA" href="javascript:inputting ('sin (3\\pi / 2)', true)">sin (3\pi / 2)</a>
	<a class="GreetingA" href="javascript:inputting ('cos**-1 x', true)">cos**-1 x</a>
	<a class="GreetingA" href="javascript:inputting ('\\log_2{8}', true)">\log_2{8}</a>
	<a class="GreetingA" href="javascript:inputting ('\\lim_{x \\to \\infty} 1/x', true)">\lim_{x \to \infty} 1/x</a>
	<a class="GreetingA" href="javascript:inputting ('Limit (1/x, x, 0, dir=\'-\')', true)">Limit (1/x, x, 0, dir='-')</a>
	<a class="GreetingA" href="javascript:inputting ('\\sum_{n=0}^oo x^n / n!', true)">\sum_{n=0}^oo x^n / n!</a>
	<a class="GreetingA" href="javascript:inputting ('\\sum_{n=1}**10 Sum (\\sum_{l=1}^m l, (m, 1, n))', true)">\sum_{n=1}**10 Sum (\sum_{l=1}^m l, (m, 1, n))</a>
	<a class="GreetingA" href="javascript:inputting ('Derivative (\\int dx, x)', true)">Derivative (\int dx, x)</a>
	<a class="GreetingA" href="javascript:inputting ('d**6/dxdy**2dz**3 x^3 y^3 z^3', true)">d**6/dxdy**2dz**3 x^3 y^3 z^3</a>
	<a class="GreetingA" href="javascript:inputting ('Integral (e^{-x^2}, (x, 0, \\infty))', true)">Integral (e^{-x^2}, (x, 0, \infty))</a>
	<a class="GreetingA" href="javascript:inputting ('\\int_0^1 \\int_0^x \\int_0^y 1 dz dy dx', true)">\int_0^1 \int_0^x \int_0^y 1 dz dy dx</a>
	<a class="GreetingA" href="javascript:inputting ('\\int_0^\\infty e^{-st} dt', true)">\int_0^\infty e^{-st} dt</a>
	<a class="GreetingA" href="javascript:inputting ('expand {x+1}**2', true)">expand {x+1}**2</a>
	<a class="GreetingA" href="javascript:inputting ('factor (x^3 + 3x^2 + 3x + 1)', true)">factor (x^3 + 3x^2 + 3x + 1)</a>
	<a class="GreetingA" href="javascript:inputting ('series (e^x, x, 1, 9)', true)">series (e^x, x, 1, 9)</a>

	<br><br>
	<div align="center">
	Copyright (c) 2019 Tomasz Pytel. <a href="javascript:window.open ('https://github.com/Pristine-Cat/SymPad')" style="color: #0007">SymPad on GitHub</a>
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
	h3 { margin: 2em 0 1em 0; }
	p { margin: 0 0 1.2em 1em; line-height: 150%; }
	i { color: red; }
</style>

<script type="text/javascript" src="https://code.jquery.com/jquery-3.4.1.js" integrity="sha256-WpOohJOqMqqyKL9FccASB9O0KwACQJpFTUBLTYOVvVU=" crossorigin="anonymous"></script>
<script type="text/javascript" src="script.js"></script>
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

<h2 align="center" style="margin: 0">SymPad</h2>
<h5 align="center" style="margin: 0">v0.2</h5>
<br>

<h3>Introduction</h3>

<p>
Sympad is a simple symbolic calculator. It is a labor of love and grew out of a desire for an easy way to calculate a quick integral while
studying some math without having to start a shell every time and import a packaged or fire up a browser and navigate to a site (technincally
that last bit is exactly what happens but the response time is better :) This desire for simplicity led to the single script option "sympad.py"
which I could plop down on my desktop and execute when needed.
</p><p>
As said, SymPad is a symbolic calculator using SymPy for the math and MathJax for the display in a web browser. It runs as a private web server
on your machine and executes the system default browser pointing to itself on startup. User input is intended to be quick, easy and intuitive and
is displayed in symbolic form as it is being entered. Sympad will accept LaTeX math formatting as well as Python expressions (or a mix) and
evaluate the result symbolically or numerically. The best way to see what it can do is to try a few things...
</p>

<h3>Quick Start</h3>

<p>
Try entering any of the following into SymPad:
</p><p>
? sqrt 2<br>
sin (3\pi / 2)<br>
cos**-1 x<br>
\log_2{8}<br>
\lim_{x \to \infty} 1/x<br>
Limit (1/x, x, 0, dir='-')<br>
\sum_{n=0}^oo x^n / n!<br>
\sum_{n=1}**10 Sum (\sum_{l=1}^m l, (m, 1, n))<br>
Derivative (\int dx, x)<br>
d**6/dxdy**2dz**3 x^3 y^3 z^3<br>
Integral (e^{-x^2}, (x, 0, \infty))<br>
\int_0^1 \int_0^x \int_0^y 1 dz dy dx<br>
\int_0^\infty e^{-st} dt<br>
expand {x+1}**2<br>
factor (x^3 + 3x^2 + 3x + 1)<br>
series (e^x, x, 1, 9)<br>
</p>

<h3>Usage</h3>

<p>
You enter expresstions and they get evaluated. The expressions may be in normal Pythonic style like "<b>a * (b + sin (x)**2 + 3/4) / 2</b>",
LaTeX such as "<b>a\frac{b+\sin^2{x}+\frac34}{2}</b>" or a mix "<b>a * (b + \sin**x{2} + \frac34) / 2</b>". The input is displayed symbolically as
you type. Input history is supported with the up and down arrows.
</p><p>
The symbolic expressions can be copied to the clipboard in various formats. Single-click for a simple short format meant to be pasted back into the
input field. A double click-copies the expression in Python format suitable for pasting into a Python shell or source file. Note in this case that
"<b>e</b>" is copied as "<b>e</b>" and not the SymPy "<b>E</b>", "<b>i</b>" is copied as "<b>i</b>" and not "<b>I</b>" or "<b>1j</b>". Simply set
"<b>e = E</b>" and "<b>i = I</b>" or "<b>i = 1j</b>" in the Python context depending on need. Finally a triple-click will copy the expression in
LaTeX format. The simple and LaTeX formats should be directly pasteable into SymPad whereas the Python representation may or may not be depending
on what elements it includes.
</p><p>
There is a special use for the "<b>_</b>" character which has the same meaning as in the Python interactive shell in that it represents the last
expression successfully evaluated. To see this in action type in "<b>1</b>" and hit Enter, then type in "<b>expand ((x+1)*_)</b>" and hit Enter.
Repeat this several times using the up arrow.
</p>

<h3>Numbers</h3>

<p>
Numbers take the standard integer or floating point form or exponential form such as 123, -2.567, 1e+100, 3E-45 or -1.521e22.
Keep in mind that "<b>e</b>" is the Euler"s number constant $e$ and if you are trying to enter 2 times $e$ plus 22 then do not write it all together
as "<b>2e+22</b>" as this will be interpreted to be 2 * 10^22, use spaces and/or explicit multiplication: 2 * e + 22.
</p>

<h3>Variables</h3>

<p>
Variable names mostly follow LaTeX convention, they are single latin letters "<b>x</b>", "<b>y</b>", "<b>z</b>", "<b>A</b>", "<b>B</b>", ... or
single greek letters preceded by a backslash such as "<b>\alpha</b>" ($\alpha$), "<b>\beta</b>" ($\beta$), \Psi ($\Psi$), etc... The variable names
"<b>i</b>", "<b>e</b>" and "<b>\pi</b>" represent their respective mathematical constants $i$, $e$ and $\pi$. There are a few special case variables
which are parsed as constants without a slash, those are "<b>pi</b>" without the slash and "<b>oo</b>" which represents "<b>\infty</b>" or $\infty$,
"<b>True</b>" and "<b>False</b>", as well as "<b>undefined</b>". The last one is what you get if you try to divide 0 by 0.
</p><p>
Variable names may be followed by various primes ' such as "<b> a' </b>" ($a'$) or "<b> \omega'' </b>" ($\omega''$).
Variables may be subscripted with other variables or numbers "<b>x_1</b>" ($x_1$), "<b>y_z</b>" ($y_z$), "<b>\alpha_\omega</b>" ($\alpha_\omega$).
This can be extended to silly levels "<b> \gamma_{x_{y_0'}''}''' </b>" ($\gamma_{x_{y_0'}''}'''$).
</p><p>
Differentials entered as "<b>dx</b>", "<b>\partialx</b>" or "<b>\partial x</b>" and are treated as a single variable. If you want to enter "<b>d</b>"
* "<b>x</b>" multiplied implicitly then put a space between them or two spaces between the "<b>\partial</b>" and the "<b>x</b>".
</p>

<h3>Strings</h3>

<p>
These exist for the sole purpose of passing string arguments to SymPy functions. They work as expected being enclosed by single or double quotes and
supporting escape sequences.
</p>

<h3>Parentheses</h3>

<p>
Explicit "<b>( )</b>" or implicit curly "<b>{ }</b>" parentheses allow prioritization of lower precedence operations over higher ones as usual and also
delineate an expression as an input to a function. They may be used interchangeably mostly, the only difference being that the implicit version is not
drawn if it does not need to be. The case where explicit "<b>( )</b>" parentheses are needed ... explicitly ... is when calling functions in general and
always when calling functions which take multiple parameters like "<b>$atan2(-1,-2)</b>".
</p>

<h3>Addition and Multiplication</h3>

<p>
Addition is addition and subtraction is subtraction: "<b>a + b</b>", "<b>a - b</b>". Multiplication is explicit with a "<b>*</b>" operator or implicit
simply by writing two symbols next to each other so that "<b>a * b</b>" is the same as "<b>ab</b>". There is however a difference between the two in that
the implicit version has a higher precedence than the explicit, which means that explicit multiplication will end a limit, sum, derivative or division
"<b>/</b>" expression whereas implicit multiplication will not, e.g. "<b>1/xy</b>" = $\frac{1}{xy}$ whereas "<b>1/x*y</b>" = $\frac{1}{x} \cdot y$.
</p><p>
Division also has two operators, the normal "<b>/</b>" which has a fairly low precedence and the LaTeX "<b>\frac</b>" version which has a very high
precedence, even higher than exponentiation. So high in fact that parentheses are not needed if using "<b>\frac</b>" as an exponent as in
"<b>x^\frac{1}{2}</b>" = $x^\frac{1}{2}$. The "<b>\frac</b>" operation also does not need parentheses if using single digit operands or single letter
variables (latin or greek) such as "<b>\frac12</b>" = $\frac12$, "<b>\frac\alpha\beta</b>" = $\frac\alpha\beta$ or "<b>\fracxy</b>" = $\frac xy$ (although
this last version without a space before the x is not legal in LaTeX but convenient for quick typing here).
</p>

<h3>Exponentiation</h3>

<p>
There are two power opearators "<b>^</b>" and "<b>**</b>". They have the same precedence and can be used interchangeably but follow slightly different
parsing rules. The "<b>^</b>" operator follows LaTeX rules which only allow a single positive digit or letter variable (lating or greek) without the use
of curly braces whereas the "<b>**</b>" follows Python rules which allow negative values or variables or functions. To illustrate the diffference:
"<b>x**-2</b>" = $x^{-2}$ whereas "<b>x^-2</b>" = $x^-2$ (which makes no sense). Also, "<b>e**log(x)</b>" will work as expected $e^{\log(x)}$ whereas
"<b>e^log(x)</b>" = $e^log(x)$.
</p>

<h3>Logarithms</h3>

<p>
The natural logarithm of x is specified by "<b>lnx</b>", "<b>\ln x</b>", "<b>log x</b>", "<b>\log{x}</b>". A logarithm in a specific base is specified
by "<b>\log_b x</b>" = $\log_b x$, "<b>log_{10}(1000)</b>" = $\log_{10} {1000}$ = 3, etc...
</p>

<h3>Roots</h3>

<p>
The square root of x ($\sqrt{x}$) may be entered in any of these forms "<b>sqrtx</b>", "<b>\sqrt x</b>", "<b>sqrt (x)</b>", "<b>\sqrt{x}</b>", with or
without the backslash. The cube (or any other) root is similar, $\sqrt[3]x$ = "<b>sqrt[3]x</b>", "<b>sqrt[3] (x)</b>" or "<b>\sqrt[3] {x}</b>".
</p>

<h3>Limits</h3>

<p>
To take the limit of an expression "<b>z</b>" as variable "<b>x</b>" approaches "<b>y</b>" enter "<b>\lim_{x \to y} (z)</b>" = $\lim_{x\to y} (z)$.
This will only give the limit if it exists and is the same when approaching from both directions, unlike SymPy which defaults to approaching from the
positive direction. To specify a direction add "<b>^+</b>" or "<b>^-</b>" to the equation as such: "<b>\lim_{x \to 0^+} 1/x</b>" = $\lim_{x\to 0^+}
\frac1x$ = $\infty$ and "<b>\lim_{x \to 0^-} 1/x</b>" = $\lim_{x\to 0^-} \frac1x$ = $-\infty$. Addition and explicit multiplication terminate a limit
expression. Limits may also be entered using the standard SymPy syntax "<b>Limit (expression, variable, to)</b>", this defaults to limit from positive
direction like SymPy, or you may specify a direction "<b>Limit (expression, variable, to, dir='+-')</b>".
</p>

<h3>Sums</h3>

<p>
The summation (finite or infinite) of expression "<b>z</b>" as variable "<b>n</b>" ranges from "<b>a</b>" to "<b>b</b>" is written as "<b>\sum_{n=a}^b
(z)</b>" = $\sum_{n=a}^b (z)$. Iterated sums work as expected, "<b>\sum_{n=1}^3 \sum_{m=1}^n m</b>" = $\sum_{n=1}^3 \sum_{m=1}^n m$ = 10. Addition and
explicit multiplication terminate a sum expression.
Sums may also be entered using the standard SymPy syntax "<b>Sum (expression, (variable, from, to))</b>".
</p>

<h3>Differentiation</h3>

<p>
The derivative of expression "<b>z</b>" with respect to "<b>x</b>" is entered as "<b>d/dx z</b>" or "<b>\frac{d}{dx} z</b>" = $\frac{d}{dx} z$. The
second derivative is "<b>d^2/dx^2 (z)</b>" or "<b>\frac{d^2}{dx^2} (z)</b>" = $\frac{d^2}{dx^2} (z)$. Using "<b>\partial</b>" ($\partial$) is allowed but
must be consistent within the expression. Mixed derivatives are entered as "<b>d^2/dxdy (z)</b>" or "<b>\partial^2 / \partial x\partial y (z)</b>" =
$\frac{\partial^2}{\partial x\partial y} (z)$. Derivatives may also be entered using the standard SymPy syntax "<b>Derivative (expression, var1, var2,
power2, ...)</b>".
</p>

<h3>Integration</h3>

<p>
The anti-derivative of expression "<b>z</b>" with respect to x is written as "<b>\int z dx</b>" = $\int z\ dx$. The definite integral from "<b>a</b>" to
"<b>b</b>" is "<b>\int_a^b z dx</b>" = $\int_a^b z\ dx$. "<b>\int dx/x</b>" = $\int \frac1x\ dx$. Iterated and improper integrals also work. Integrals
may also be entered using the standard SymPy syntax "<b>Integral (expression, (variable, from, to))</b>".
</p>

<h3>Functions</h3>

<p>
Currently several SymPy functions are supported directly by SymPad, with a mechanism for calling any other existing SymPy function explicitly. For a
function to be supported directly means that you can type the function name without the "<b>$</b>" escape character and that SymPad understands how the
function works and what it returns. See notes for list of directly supported functions / objects.
</p><p>
The standard trigonometric and hyperbolic functions and their inverses can be entered as usual, with or without leading backslash: "<b>sin</b>",
"<b>\cos</b>", "<b>arctan</b>", "<b>\acscsh</b>", etc... In addition these functions accept a special commonly used syntax for exponentiation or for
inverses as a convenience. For example "<b>sin^2(x)</b>" = $\sin^2(x)$ and "<b>\tan^{-1}x</b>" = $\tan^{-1}x$ = $\arctan(x)$.
</p><p>
Other SymPy functions are supported directly such as "<b>simplify (sin(x) / cos(x))</b>" = $\tan(x)$, "<b>expand ({x+1}^3)</b>" = $x^3+3x^2+3x+1$ and
"<b>factor (x^2 + 2x + 1)</b>" = $(x+1)^2$. Functions don't technically REQUIRE explicit or implicit parentheses but for any parameter more complicated
than another function or variable to a power they will be needed, as well as if the function takes more than one parameter in which case explicit
parentheses are needed.
</p><p>
Three functions have a special separate syntax. The functions "<b>abs/Abs (x)</b>" are equivalent to the standard bar syntax for absolute value
"<b>|x|</b>", the "<b>factorial (x)</b>" function is identical to writing "<b>x!</b>" and "<b>exp (x)</b>" is the same as writing "<b>e^x</b>". In fact
those functions are translated on the fly.
</p><p>
If a SymPy function is not supported directly (and the vast majority are not) then it can still be called using a special leading escape character
"<b>\($\)</b>". To call the SymPy "<b>sign</b>" function for example simply enter "<b>\($\)sign (-2)</b>". Functions may take multiple comma-separated
arguments with optional keyword arguments as well. The keyword argument identifier implementation is hacked into the grammar so if a keyword name can not
be entered directly then try entering as a string like "<b>'this_name_has_too__many___underscores' = value</b>".
</p><p>
There is a special function "<b>?</b>", this is equivalent to SymPy "<b>N ()</b>" or "<b>evalf ()</b>" and it will ask SymPy to numerically evaluate
whatever it can in the given expression. This is how you would get the numerical value of $\sqrt 2$ or $\sin(2)$ writing "<b>? sqrt 2</b>" or
"<b>? (\sin{2})</b>".
</p>

<h3>Notes</h3>

<p>
Due to mixing operators from Python and LaTeX the grammar may be a little wonky in places so if something doesn't seem to work as it should try wrapping
it in parentheses or putting a space between the problematic elements.
</p><p>
There are many SymPy objects which SymPad does not understand natively yet. In any case where such an object is the result of an evalutation then the
SymPy LaTeX representation will be used for the displayed answer and the SymPy str version of the object will be used as the Python copy string. This may
or may not allow you to paste the Python string back into SymPad to continue working with the result, you will probably need to "<b>$</b>" escape function
and object names. A single-click copy of the result will have the element which was not understood replaced with "<b>undefined</b>".
</p><p>
Directly supported functions: Abs, Derivative, Integral, Limit, Piecewise, Sum, abs, arg, exp, expand, factor, factorial, ln, series, simplify.
</p>

<h3>Future</h3>

<p>
Time and interest permitting: Vectors and matrices, assumptions / hints, stateful variables, piecewise expressions, long Python variable names, plots.
<p></p>
</p>

<br><br><br>
<div align="center">
Copyright (c) 2019 Tomasz Pytel, All rights reserved.
<br><br>
SymPad on GitHub: <a href="javascript:window.open ('https://github.com/Pristine-Cat/SymPad')">https://github.com/Pristine-Cat/SymPad</a>
</div>

</body>
</html>""".encode ("utf8"),
}

import re
import types

#...............................................................................................
class Incomplete (Exception):
	def __init__ (self, reduct):
		self.reduct = reduct

class Token (str):
	def __new__ (cls, str_, text = None, pos = None, grps = None):
		self      = str.__new__ (cls, str_)
		self.text = text or ''
		self.pos  = pos
		self.grp  = () if not grps else grps

		return self

class Parser:
	_PARSER_TABLES = '' # placeholders so pylint doesn't have a fit
	_PARSER_TOP    = ''
	TOKENS         = {}

	_rec_SYMBOL_NUMTAIL = re.compile (r'(.*[^_\d])(_?\d+)?') # symbol names in code have extra digits at end for uniqueness which are discarded

	def __init__ (self):
		if isinstance (self._PARSER_TABLES, bytes):
			import ast, base64, zlib
			symbols, rules, strules, terms, nterms = ast.literal_eval (zlib.decompress (base64.b64decode (self._PARSER_TABLES)).decode ('utf8'))
		else:
			symbols, rules, strules, terms, nterms = self._PARSER_TABLES

		self.tokgrps = {} # {'token': (groups pos start, groups pos end), ...}
		tokpats      = list (self.TOKENS.items ())
		pos          = 0

		for tok, pat in tokpats:
			l                   = re.compile (pat).groups + 1
			self.tokgrps [tok]  = (pos, pos + l)
			pos                += l

		self.tokre   = '|'.join (f'(?P<{tok}>{pat})' for tok, pat in tokpats)
		self.tokrec  = re.compile (self.tokre)
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

			if name [0] != '_' and type (obj) is types.MethodType and obj.__code__.co_argcount >= 2:
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

	def parse_success (self, reduct):
		'NO PARSE_SUCCESS'
		return None # True to contunue checking conflict backtracks, False to stop and return

	def parse (self, src):
		has_parse_success = (self.parse_success.__doc__ != 'NO PARSE_SUCCESS')

		rules, terms, nterms, rfuncs = self.rules, self.terms, self.nterms, self.rfuncs

		tokens = self.tokenize (src)
		tokidx = 0
		cstack = [] # [(action, tokidx, stack, stidx, extra state), ...] # conflict backtrack stack
		stack  = [(0, None, None)] # [(stidx, symbol, reduction) or (stidx, token), ...]
		stidx  = 0
		rederr = None # reduction function raised SyntaxError

		while 1:
			if not rederr:
				tok       = tokens [tokidx]
				act, conf = terms [stidx].get (tok, (None, None))

			if rederr or act is None:
				rederr = None

				self.tokens, self.tokidx, self.cstack, self.stack, self.stidx, self.tok = \
						tokens, tokidx, cstack, stack, stidx, tok

				if tok == '$end' and stidx == 1 and len (stack) == 2 and stack [1] [1] == rules [0] [1]:
					if not has_parse_success:
						return stack [1] [2]

					if not self.parse_success (stack [1] [2]) or not cstack:
						return None

				elif self.parse_error ():
					tokidx, stidx = self.tokidx, self.stidx
					continue

				elif not cstack:
					if has_parse_success: # do not raise SyntaxError if parser relies on parse_success
						return None

					raise SyntaxError ( \
						'unexpected end of input' if tok == '$end' else \
						f'invalid token {tok.text!r}' if tok == '$err' else \
						f'invalid syntax {src [tok.pos : tok.pos + 16]!r}')

			# if act is None:
				act, tokens, tokidx, stack, stidx, estate = cstack.pop ()
				tok                                       = tokens [tokidx]

				self.parse_setextrastate (estate)

			elif conf is not None:
				cstack.append ((conf, tokens [:], tokidx, stack [:], stidx, self.parse_getextrastate ()))

			if act > 0:
				tokidx += 1
				stidx   = act

				stack.append ((stidx, tok))

			else:
				rule  = rules [-act]
				rnlen = -len (rule [1])
				prod  = rule [0]

				try:
					reduct = rfuncs [-act] (*(t [-1] for t in stack [rnlen:]))

				except SyntaxError as e:
					rederr = e or True
					continue

				except Incomplete as e:
					rederr = True
					reduct = e.reduct

				del stack [rnlen:]

				stidx = nterms [stack [-1] [0]] [prod]

				stack.append ((stidx, prod, reduct))

class lalr1: # for single script
	Incomplete = Incomplete
	Token      = Token
	Parser     = Parser
import re

# ('=', 'rel', lhs, rhs)        - equality of type 'rel' relating Left-Hand-Side and Right-Hand-Side
# ('#', 'num')                  - numbers represented as strings to pass on maximum precision to sympy
# ('@', 'var')                  - variable name, can take forms: 'x', "x'", 'dx', '\partial x', 'x_2', '\partial x_{y_2}', "d\alpha_{x_{\beta''}'}'''"
# ('"', 'str')                  - string (for function parameters like '+' or '-')
# (',', (expr1, expr2, ...))    - comma expression (tuple)
# ('(', expr)                   - explicit parentheses
# ('|', expr)                   - absolute value
# ('-', expr)                   - negative of expression, negative numbers are represented with this at least initially
# ('!', expr)                   - factorial
# ('+', (expr1, expr2, ...))    - addition
# ('*', (expr1, expr2, ...))    - multiplication
# ('/', numer, denom)           - fraction numer(ator) / denom(inator)
# ('^', base, exp)              - power base ^ exp(onent)
# ('log', expr)                 - natural logarithm of expr
# ('log', expr, base)           - logarithm of expr in base
# ('sqrt', expr)                - square root of expr
# ('sqrt', expr, n)             - nth root of expr
# ('func', 'func', expr)        - sympy or regular python function 'func', will be called with sympy expression
# ('lim', expr, var, to)        - limit of expr when variable var approaches to from both positive and negative directions
# ('lim', expr, var, to, 'dir') - limit of expr when variable var approaches to from specified direction dir which may be '+' or '-'
# ('sum', expr, var, from, to)  - summation of expr over variable var from from to to
# ('diff', expr, (var1, ...))   - differentiation of expr with respect to var1 and optional other vars
# ('intg', expr, var)           - anti-derivative of expr (or 1 if expr is None) with respect to differential var ('dx', 'dy', etc ...)
# ('intg', expr, var, from, to) - definite integral of expr (or 1 if expr is None) with respect to differential var ('dx', 'dy', etc ...)

#...............................................................................................
class AST (tuple):
	op = None

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

	def __getattr__ (self, name): # calculate value for nonexistent self.name by calling self._name ()
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

	def strip_paren (self, count = None):
		count = 999999999 if count is None else count

		while self.op == '(' and count:
			self   = self.paren
			count -= 1

		return self

	def strip_minus (self, count = None):
		count = 999999999 if count is None else count

		while self.op == '-' and count:
			self   = self.minus
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
	def is_int_text (text): # >= 0
		return AST_Num._rec_int.match (text)

	@staticmethod
	def flatcat (op, ast0, ast1): # ,,,/O.o\,,,~~
		if ast0.op == op:
			if ast1.op == op:
				return AST (op, ast0 [-1] + ast1 [-1])
			return AST (op, ast0 [-1] + (ast1,))
		elif ast1.op == op:
			return AST (op, (ast0,) + ast1 [-1])
		return AST (op, (ast0, ast1))

#...............................................................................................
class AST_Eq (AST):
	op, is_eq  = '=', True

	SHORT2LONG = {'!=': '\\ne', '<=': '\\le', '>=': '\\ge'}
	LONG2SHORT = {'\\ne': '!=', '\\le': '<=', '\\ge': '>=', '==': '=', '\\neq': '!=', '\\lt': '<', '\\gt': '>'}

	def _init (self, rel, lhs, rhs):
		self.rel = rel # should be short form
		self.lhs = lhs
		self.rhs = rhs

	def _is_eq_eq (self):
		return self.rel == '='

class AST_Num (AST):
	op, is_num = '#', True

	_rec_int          = re.compile (r'^-?\d+$')
	_rec_pos_int      = re.compile (r'^\d+$')
	_rec_mant_and_exp = re.compile (r'^(-?\d*\.?\d*)[eE](?:(-\d+)|\+?(\d+))$')

	def _init (self, num):
		self.num = num

	def _is_pos_num (self):
		return self.num [0] != '-'

	def _is_neg_num (self):
		return self.num [0] == '-'

	def _is_pos_int (self):
		return AST_Num._rec_pos_int.match (self.num)

	def mant_and_exp (self):
		m = AST_Num._rec_mant_and_exp.match (self.num)

		return (self.num, None) if not m else (m.group (1) , m.group (2) or m.group (3))

class AST_Var (AST):
	op, is_var = '@', True

	TEXTVARS   = ('True', 'False', 'undefined')
	LONG2SHORT = {'\\pi': 'pi', '\\infty': 'oo', **dict ((f'\\text{{{v}}}', v) for v in TEXTVARS)}
	SHORT2LONG = {'pi': '\\pi', 'oo': '\\infty', **dict ((v, f'\\text{{{v}}}') for v in TEXTVARS)}

	_rec_diff_start         = re.compile (r'^d(?=[^_])')
	_rec_part_start         = re.compile (r'^\\partial ')
	_rec_diff_or_part_start = re.compile (r'^(d(?=[^_])|\\partial )')
	_rec_diff_or_part_solo  = re.compile (r'^(?:d|\\partial)$')
	_rec_not_single         = re.compile (r"^(?:d.|\\partial |.+[_'])")
	_rec_as_short_split     = re.compile ('(' + '|'.join (v.replace ('\\', '\\\\') for v in LONG2SHORT) + ')')

	def _init (self, var):
		self.var = var # should be long form

	def _is_null_var (self):
		return not self.var

	def _has_short_var (self):
		return self.var in AST_Var.LONG2SHORT

	def _is_differential (self):
		return AST_Var._rec_diff_start.match (self.var)

	def _is_partial (self):
		return AST_Var._rec_part_start.match (self.var)

	def _is_diff_or_part (self):
		return AST_Var._rec_diff_or_part_start.match (self.var)

	def _is_diff_or_part_solo (self):
		return AST_Var._rec_diff_or_part_solo.match (self.var)

	def _is_single_var (self): # is single atomic variable (non-differential, non-subscripted, non-primed)?
		return not AST_Var._rec_not_single.match (self.var)

	def as_var (self): # 'x', dx', '\\partial x' -> 'x'
		return AST ('@', AST.Var._rec_diff_or_part_start.sub ('', self.var))

	def as_differential (self): # 'x', 'dx', '\\partial x' -> 'dx'
		return AST ('@', f'd{AST_Var._rec_diff_or_part_start.sub ("", self.var)}') if self.var else self

	def as_partial (self): # 'x', 'dx', '\\partial x' -> '\\partial x'
		return AST ('@', f'\\partial {AST_Var._rec_diff_or_part_start.sub ("", self.var)}') if self.var else self

	def diff_or_part_start_text (self): # 'dx' -> 'd', '\\partial x' -> '\\partial '
		m = AST_Var._rec_diff_or_part_start.match (self.var)

		return m.group (1) if m else ''

	def as_short_var_text (self):
		vs = AST_Var._rec_as_short_split.split (self.var)
		vs = [AST_Var.LONG2SHORT.get (v, v) for v in vs]

		return ''.join (vs)

class AST_Str (AST):
	op, is_str = '"', True

	def _init (self, str_):
		self.str_ = str_

class AST_Comma (AST):
	op, is_comma = ',', True

	def _init (self, commas):
		self.commas = commas

class AST_Paren (AST):
	op, is_paren = '(', True

	def _init (self, paren):
		self.paren = paren

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

class AST_Mul (AST):
	op, is_mul = '*', True

	def _init (self, muls):
		self.muls = muls

class AST_Div (AST):
	op, is_div = '/', True

	def _init (self, numer, denom):
		self.numer = numer
		self.denom = denom

class AST_Pow (AST):
	op, is_pow = '^', True

	def _init (self, base, exp):
		self.base = base
		self.exp  = exp

class AST_Log (AST):
	op, is_log = 'log', True

	def _init (self, log, base = None):
		self.log  = log
		self.base = base

class AST_Sqrt (AST):
	op, is_sqrt = 'sqrt', True

	def _init (self, rad, idx = None):
		self.rad = rad
		self.idx = idx

class AST_Func (AST):
	op, is_func = 'func', True

	PY_ONLY = set ('''
		?
		Abs
		Derivative
		Integral
		Limit
		Piecewise
		Sum
		abs
		expand
		factor
		factorial
		series
		simplify
		'''.strip ().split ())

	PY_AND_TEX = set ('''
		arg
		exp
		ln
		'''.strip ().split ())

	PY_ALL = PY_ONLY | PY_AND_TEX
	ALIAS  = {'?': 'N'}

	_rec_trigh             = re.compile (r'^a?(?:sin|cos|tan|csc|sec|cot)h?$')
	_rec_trigh_noninv_func = re.compile (r'^(?:sin|cos|tan|csc|sec|cot)h?$')

	def _init (self, func, arg):
		self.func = func
		self.arg  = arg

	def _is_trigh_func (self):
		return AST_Func._rec_trigh.match (self.func)

	def _is_trigh_func_noninv_func (self):
		return AST_Func._rec_trigh_noninv_func.match (self.func)

class AST_Lim (AST):
	op, is_lim = 'lim', True

	def _init (self, lim, lvar, to, dir = None):
		self.lim  = lim
		self.lvar = lvar
		self.to   = to
		self.dir  = dir

class AST_Sum (AST):
	op, is_sum = 'sum', True

	def _init (self, sum, svar, from_, to):
		self.sum   = sum
		self.svar  = svar
		self.from_ = from_
		self.to    = to

class AST_Diff (AST):
	op, is_diff = 'diff', True

	def _init (self, diff, dvs):
		self.diff = diff
		self.dvs  = dvs

class AST_Intg (AST):
	op, is_intg = 'intg', True

	def _init (self, intg, dv, from_ = None, to = None):
		self.intg  = intg
		self.dv    = dv
		self.from_ = from_
		self.to    = to

#...............................................................................................
_AST_OP2CLS = {
	'=': AST_Eq,
	'#': AST_Num,
	'@': AST_Var,
	'"': AST_Str,
	',': AST_Comma,
	'(': AST_Paren,
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
}

_AST_CLS2OP = dict ((b, a) for (a, b) in _AST_OP2CLS.items ())

for cls in _AST_CLS2OP:
	setattr (AST, cls.__name__ [4:], cls)

AST.Zero      = AST ('#', '0')
AST.One       = AST ('#', '1')
AST.NegOne    = AST ('#', '-1')
AST.VarNull   = AST ('@', '')
AST.I         = AST ('@', 'i')
AST.E         = AST ('@', 'e')
AST.Pi        = AST ('@', '\\pi')
AST.Infty     = AST ('@', '\\infty')
AST.True_     = AST ('@', '\\text{True}')
AST.False_    = AST ('@', '\\text{False}')
AST.Undefined = AST ('@', '\\text{undefined}')

# if __name__ == '__main__':
# 	print (AST_Str ('a').is_str)# TODO: 1+1j complex number parsing?

# Builds expression tree from text, nodes are nested AST tuples.

# FUTURE: verify vars in expr func remaps
# FUTURE: vectors and matrices, assumptions / hints, stateful variables, piecewise expressions, long Python variable names, plots

import ast as py_ast
from collections import OrderedDict
import os
import re


def _ast_from_tok_digit_or_var (tok, i = 0):
	return AST ('#', tok.grp [i]) if tok.grp [i] else AST ('@', AST.Var.SHORT2LONG.get (tok.grp [i + 1] or tok.grp [i + 3], tok.grp [i + 2]))

def _expr_int (ast, from_to = ()): # find differential for integration if present in ast and return integral ast
	if ast.is_differential or ast.is_null_var: # null_var is for autocomplete
		return AST ('intg', None, ast, *from_to)

	elif ast.is_div:
		if ast.denom.is_mul and ast.denom.muls [-1].is_differential:
			return AST ('intg', ('/', ast.numer, ast.denom.muls [0] if len (ast.denom.muls) == 2 else \
					AST ('*', ast.denom.muls [:-1])), ast.denom.muls [-1], *from_to)

		if ast.numer.is_differential:
			return AST ('intg', ('/', ast.One, ast.denom), ast.numer, *from_to)

	elif ast.is_mul and (ast.muls [-1].is_differential or ast.muls [-1].is_null_var): # null_var is for autocomplete
		return AST ('intg', ast.muls [0] if len (ast.muls) == 2 else AST ('*', ast.muls [:-1]), ast.muls [-1], *from_to)

	elif ast.is_add:
		if ast.adds [-1].is_differential:
			return AST ('intg', \
					AST ('+', ast.adds [:-1])
					if len (ast.adds) > 2 else \
					ast.adds [0] \
					, ast.adds [-1], *from_to)

		if ast.adds [-1].is_mul and ast.adds [-1].muls [-1].is_differential:
			return AST ('intg', \
					AST ('+', ast.adds [:-1] + (AST ('*', ast.adds [-1].muls [:-1]),))
					if len (ast.adds [-1].muls) > 2 else \
					AST ('+', ast.adds [:-1] + (ast.adds [-1].muls [0],)) \
					, ast.adds [-1].muls [-1], *from_to)

	elif ast.is_intg and ast.intg is not None:
		return AST ('intg', _expr_int (ast.intg, () if ast.from_ is None else (ast.from_, ast.to)), ast.dv, *from_to)

	raise SyntaxError ('integration expecting a differential')

def _expr_diff (ast): # convert possible cases of derivatives in ast: ('*', ('/', 'd', 'dx'), expr) -> ('diff', expr, 'dx')
	def _interpret_divide (ast):
		if ast.numer.is_diff_or_part_solo:
			p = 1
			v = ast.numer.var

		elif ast.numer.is_pow and ast.numer.base.is_diff_or_part_solo and ast.numer.exp.is_pos_int:
			p = int (ast.numer.exp.num)
			v = ast.numer.base.var

		else:
			return None

		ast_dv_check = (lambda n: n.is_differential) if v [0] == 'd' else (lambda n: n.is_partial)

		ns = ast.denom.muls if ast.denom.is_mul else (ast.denom,)
		ds = []
		cp = p

		for i in range (len (ns)):
			n = ns [i]

			if ast_dv_check (n):
				dec = 1
			elif n.is_pow and ast_dv_check (n.base) and n.exp.is_pos_int:
				dec = int (n.exp.num)
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
						tail.insert (0, AST ('diff', ast.muls [i + 1] if i == end - 2 else AST ('*', ast [i + 1 : end]), diff.dvs))

					else:
						continue

					end = i

		if tail:
			tail = tail [0] if len (tail) == 1 else AST ('*', tuple (tail))

			return tail if end == 0 else AST.flatcat ('*', ast.muls [0], tail) if end == 1 else AST.flatcat ('*', AST ('*', ast.muls [:end]), tail)

	return ast

def _expr_func (iparm, *args): # rearrange ast tree for explicit parentheses like func (x)^y to give (func (x))^y instead of func((x)^y)
	if args [iparm].is_fact:
		if args [iparm].fact.is_paren:
			return AST ('!', AST (*(args [:iparm] + (args [iparm].fact.paren,) + args [iparm + 1:])))

	elif args [iparm].is_pow:
		if args [iparm].base.is_paren:
			return AST ('^', AST (*(args [:iparm] + (args [iparm].base.paren,) + args [iparm + 1:])), args [iparm].exp)

	return AST (*args)

def _expr_func_remap (remap_func, ast): # rearrange ast tree for a given function remapping like 'Derivative' or 'Limit'
	expr = _expr_func (1, '(', ast.strip_paren ())
	ast  = remap_func (expr.paren if expr.is_paren else expr [1].paren)

	return AST (expr.op, ast, *expr [2:]) if not expr.is_paren else ast

_remap_func_lim_dirs = {'+': '+', '-': '-', '+-': None}

def remap_func_lim (ast): # remap function 'Limit' to native ast representation for pretty rendering
	if ast.is_null_var:
		return AST ('lim', ast, AST.VarNull, AST.VarNull)
	elif not ast.is_comma:
		raise lalr1.Incomplete (AST ('lim', ast, AST.VarNull, AST.VarNull))

	commas = ast.commas
	l      = len (commas)

	if l == 1:
		ast = AST ('lim', commas [0], AST.VarNull, AST.VarNull)
	elif l == 2:
		ast = AST ('lim', commas [0], commas [1], AST.VarNull)
	elif l == 3:
		return AST ('lim', commas [0], commas [1], commas [2], '+')
	elif commas [3].is_str:
		return AST ('lim', commas [0], commas [1], commas [2], _remap_func_lim_dirs.get (commas [3].str_, '+'))
	elif commas [3].is_eq_eq and commas [3].lhs.as_identifier () == 'dir' and commas [3].rhs.is_str:
		return AST ('lim', commas [0], commas [1], commas [2], _remap_func_lim_dirs.get (commas [3].rhs.str_, '+'))
	else:
		ast = AST ('lim', commas [0], commas [1], commas [2])

	if commas [-1].is_null_var:
		return ast

	raise lalr1.Incomplete (ast)

def remap_func_sum (ast): # remap function 'Sum' to native ast representation for pretty rendering
	if ast.is_null_var:
		return AST ('sum', ast, AST.VarNull, AST.VarNull, AST.VarNull)
	elif not ast.is_comma:
		ast = AST ('sum', ast, AST.VarNull, AST.VarNull, AST.VarNull)

	else:
		commas = ast.commas

		if len (commas) == 1:
			ast = AST ('sum', commas [0], AST.VarNull, AST.VarNull, AST.VarNull)

		else:
			ast2 = commas [1].strip_paren (1)

			if not ast2.is_comma:
				ast = AST ('sum', commas [0], ast2, AST.VarNull, AST.VarNull)
			elif len (ast2.commas) == 3:
				return AST ('sum', commas [0], ast2.commas [0], ast2.commas [1], ast2.commas [2])

			else:
				commas = ast2.commas
				ast    = AST (*(('sum', ast.commas [0], *commas) + (AST.VarNull, AST.VarNull, AST.VarNull)) [:5])

		if commas [-1].is_null_var:
			return ast

	raise lalr1.Incomplete (ast)

def remap_func_diff (ast): # remap function 'Derivative' to native ast representation for pretty rendering
	if ast.is_null_var:
		return AST ('diff', ast, (AST.VarNull,))
	elif not ast.is_comma:
		raise lalr1.Incomplete (AST ('diff', ast, (AST.VarNull,)))
	elif len (ast.commas) == 1:
		raise lalr1.Incomplete (AST ('diff', ast.commas [0], (AST.VarNull,)))

	commas = list (ast.commas [:0:-1])
	ds     = []

	while commas:
		d = commas.pop ().as_differential ()

		if commas and commas [-1].is_num:
			ds.append (AST ('^', d, commas.pop ()))
		else:
			ds.append (d)

	return AST ('diff', ast.commas [0], AST (*ds))

def remap_func_intg (ast): # remap function 'Integral' to native ast representation for pretty rendering
	if not ast.is_comma:
		return AST ('intg', ast, ast.as_differential () if ast.is_var else AST.VarNull)
	elif len (ast.commas) == 1:
		ast = AST ('intg', ast.commas [0], AST.VarNull)

	else:
		ast2 = ast.commas [1].strip_paren (1)

		if not ast2.is_comma:
			return AST ('intg', ast.commas [0], ast2.as_differential ())
		elif len (ast2.commas) == 3:
			return AST ('intg', ast.commas [0], ast2.commas [0].as_differential (), ast2.commas [1], ast2.commas [2])
		else:
			ast = AST (*(('intg', ast.commas [0], ast2.commas [0].as_differential ()) + ast2.commas [1:] + (AST.VarNull, AST.VarNull)) [:5])

	raise lalr1.Incomplete (ast)

#...............................................................................................
class Parser (lalr1.Parser):
	_PARSER_TABLES = \
			b'eJztXXmP27gV/zIFMgZowOTjpfyXTWa3g+bYnSQLFMYiyDEpAmyO5mgLLPLd+w5KJGVZPmJ77GQwtCRSFN/B3+PjJc3Z/NaDi4dPH99Sty4ePsHj/YsHeHz8lI+/XXLSo1/w+OTy4pe/4/nnpw/vUuL5z3TvpzuXePz1zuX5w/tUxi8PH12eP7v79PL+Pynv' \
			b'5Z276aTT2eCZb1P2x08umdhPeHzIJH/n8v529e5Vm68rny7uPnrw4A6RxZL+cc5PE1vEyb1HT3+6f/74CRdwFx+gxPPfWDA+/Xqfxbx38fvFvXPKc+/RE+bhTmJCtw8yr3fuPnl0eXHnfqZGl79eXjw4p2KePMLDy+cfrz4/e//x2av3X178efXp8/OPmPrp' \
			b'y4v/8MXV/z58fPby/du3z9vIpy8frro7r7+8e/ns3dW/8s0XeFk8+u7L2/by89XH7vr1x+cv2+sPyMG7NvL8xacu/f1/u+zPX34uSWZyXYkFzT/fdKlv3nXPvf3y57M3bz+00Vdv/pMvX7/u+M2y0AN40XH26lUu9erf7XV3desPNT+bmqiMnyi5CHSh1dTw' \
			b'OaizqBqFCcapZtKmcUoXnepIV5Z/MFNTN8nxIooXRMTLwQA+OEkpeIUXWBSXFPkHyIXQ6OKznIIX9Cj+QCHfU5Ci6IK4cnIAP0nRqWYRdaPONOYyM/pNuiQoo9qmC0qjKxQF2Td2kmMQWCt1sluIQZXiF2L1E6GMIdcsEl3ZdHU248iExSadGmSyjU+F7RmK' \
			b'kyi79mZK7CJTzQrXWp0ZhVXICjIKpKoxZ9Lb4H3CCVbzOtl6uaaaa8fxD0x7J8Uhx6dcWQ3/kN/JpLvCC89qCBO5njJikYygUCNYSEBCmJm0KVG1aa5MRpaYZeSyTcNq5ysvB9ThJMUR6kwJFc+gFyRiFETvmA6FEgiUokvjOhVAV5coM+NeqiRFZ3VCQQXV' \
			b'I2igiixZxgRBNl2EdIH02ysjFU2GYrBmkCkjmmuTMI7JkzpXP0cbxygXHFgHraSJky4R1TiURrGcLlrD4lFEbIbmM4Xa86RAQOtyKihqeSwoa5V1ykZl0TIxO2azVKL1ymJmT6aIciHo7ExZraxRrlF+RsZJ1Y2VHqg20FQQtUBAQZrKOeWwBOWUV04rh0+B' \
			b'cvgIYxb5wpr1eNMrH5SPyjcqzFTQKhgVQAV8EqPNHwRG0jHQcX5GIkxEaBLrDIXhu45PgY8x3Ws4ZkFONqVaun2cklqRwjZJViOyigC6FUCnXKyJY+A6CLsgVQMcdUG5eEIgg5iESKAR0CEnpPMzn0T0rPpTNSQfRSiBlRNJ/UxEM2JIRiQ05C4OxNecmmam' \
			b'HTJtwc/hOBDVmCZz4LXyRnm8sIfjA2bXoH4qkxqYtt3UggzHUCjUgBByXtAiYHEmPXHaZiEiOdYC9mOw13KqojhxFc4mm2Y0rfeoSQ7W6A2ekZbEi/n65LaCtJ1BUBUkTxDOAnMWUKdehaBCJKZT/tbroZYmp6Z57ogg2yfEcCB+T4LTeDKcIpPE6jFzaI+b' \
			b'Q+qeG24GWJXU6yV+j4Y7L9wBnyvfOKeer1kYhDiJSg9yixY990uN9EuN9EsN90sdR53cNFaYM5x6qj4MTJKYPcahqJpUsYbr8KAdMOp8Cu3m4LRxSCNu2psDahupwnbm4NNwX8xAR4G/E/3ZE4b9nDrT5uT7n1IRTkv1zGT0rHXqYcNJV5Bh0K1p0lo0EQSo' \
			b'geu26vbOqYNspGds2FOENIclvekgM1xnQUamqDOYSDcTFnxM4LT+RFccSKUoSBSSl4Ujmkuak7+H4/H37OjhhLr11N0wqb8A0l8A6S+QFPUj0qA6AYJrluUwnIPcsZE5GpCJEjr5BHPP+D7YgF1YSRDGgqBobIRbpxO+Zyfc5FCDycqWSgzplEQL0vcLXk5c' \
			b'7wP1xyZlj8rGkQe70IYRPwJYK4C1XJucyl1ae+humRdgifawHCsoY3iBSJCMJ3ipGbaNXiuPcjmRy4lc7mTxyK3E6bJPIOI64COVI1VoxYqs1KBNraeXSvNSaXhCWgJILxldyhiOeTg9JxmCyBC4Lybz3KlDxtzXM7zIahTRozwWU8549HI2R86hPm4OqZKb' \
			b'tPY1S4tfM26bZ2o+Ywpi6zJGSSK41BjQWKygWPHcMoyNNzYYi2LmxoNVISpCrkgcloVkZFUQVnlFJku0IA72mCOiF5FrVLQqehWRb0xE8RAkWAugGqsarxqShaQlSVGcGdbHDEWZ0X4GvEdSkpgkJwlKktLiCM2r03oZLVjRyhEtG9HKDdUJTV/Q1AUtg9Ki' \
			b'Ii0okkZJm9QXJzdMK6a0DE1AoNlvp1HLnqSnXRiWtpU0vPTPO2swN96grQWer7AOp5Y2d8zYbtswpQ09tKkG0UC56OBs2qlC2SkRbwfaKUQbPFChxd8UGWowmxU+kNTU0Z4Cy8QN7+4gKigvzRXMaDcJlkT7kWjvgXNtObQlA+tiipUxxaqgwmjjEZZMW2ho' \
			b'tw0wa5iIlTilbSm0E4N22njazIJxTMaq97KNKNCPRLNUFrFAPweJGikIo0QQLwNRIy1p62STDFJoBZ060i4WZ1Hffzm4PaVK0h7P/is5d4I5ybEa5juEdolrtwace1g2DOftsLwJjkexS1DlRq0EL0cDnxJ46bJAb4lYvsXHFZiVgstAyNWCXKpQhi5L1eGW' \
			b'QNtHa368B9garTnbOFjbTW8JrUzcd1BtKQ2CVQtGM6UKpnp2m1qBRt+eStXh2X5lH36D1i3RahmttkarFbTajFa7HK2W0WpXo9X2A6PVLqLVjqO1e3wcrV22FWi1NVptjdZEaRitVtDaUVoPrXCD1m3R2jBa644BRwOfWrQ2y9HaMFqb1WhdCIzWZhGtzTha' \
			b'u8fH0dplW4HWpkZrU6M1URpGayNo7Sith1a7PloP0OE1m/d5B4E83OeF/fR7RzFNsGh4826BaY4GPiVM8+bmjGmjcyjxzdn4uALfZQGpGFpu1jW+U7eXiQhXRko3sX2qh/dc3Cjec7YlnV9TwZ7Ly7BnfpKwgvyW5iDyOXtT0lwL+e4G+ftFPveUTd1TNtJT' \
			b'NrmnbOqesjE5VMjnXrNZ3WsuC0jFEPLNMPKl52xM2uYvyJeEPvK74saR32VbhnxTIb/uTBvpTJs89GtpDiNf+tMFzbWQ72+Qv1/kAyMfauSDIB8y8qFGPuRQIR8Y+bAa+dAPjHwYRj4I8kG1r1CZ2D7VR35X3Djyu2zLkA8V8qFGPgjyISM/0RxGPgjyM821' \
			b'kB9ukL9f5PN409TjTSPjTZPHm6YebxqbQ4V8Hnua1WPPsoBUjI1yGkC+jD/5hTsp3cT2qT7yu+LGkd9lW4Z8WyG/HpIaGZJynoT8RHMY+TIqLWiuhfx4g/z9Ij8y8mON/CjIjxn5sUZ+zKFCfmTkx9XIj/3AyI/DyI+C/CjIj4J8yd5HfndjHPldtmXIjxXy' \
			b'Y438KMiPGfmJ5jDyoyA/01wL+Q0h3yhIC0db4j9ehwm4BStwQ4s8u7QFvSt7oOkIxS91o7LINOppHSPTOiZP65h6Wsc0OZSmQZvIeJbHrJ7lMQuBraMZtg6Z6aGTkdKl0plazzo4lZRqBmZ+6A1fsH1L6ThYZilNZSn1RJCRiSDOY7hG2FqkwCXWIvNBBd21' \
			b'rEXPvtFRXIuhnJav4O8R8FcJCoMAmROCPCcE9ZwQKbQNlUFYycnHFQZRlpFKsvJ9hAGDAJkWApkWgvS6vjzVM4hc3Ki7yNmWGAFU00JQTwuBTAtBnhZqaQ4aAMi0UEFzPQPYYG30pqe0Dfp5XgjqeSGQeSHI80JQzwuByaFEP2fj4yrom35g6A/PC4HMC6WJ' \
			b'f5B5oZTQh35X3Dj0u2zLoF/NC0E9LwQyLwR5XqilOQx9mRcqaK4H/Q0WWq8F+kNbek4N/TxChnqEDDJChjxChnqETPsP21Chn0fIsHqEXBaQiiH05xEyl5HALwNkkAEyyAA5P9fHf3djHP9dtmX4r8bIUI+RQcbIkMfILc1h/MsYuaA5gH9nb5OmB8xggxXc' \
			b'GzPY0gx4AxgdSzPwYgZ5DxjUm8AIAm2ozIB3gcHqbWBlAakYMgOfzcBnM5DdYHQyktXE4rm+GXQ3xs2gy7bMDHxlBvXOMGYpkU9mkGgOm4EXM8g0NzKDY18a/h7MILAZhNoMgphByGYQajMIOVRmENgMwmozCP3AZhCyGRRdoSBmEMQMgphB91zfDLob42bQ' \
			b'ZVtmBqEyg1CbQRAzCNkMEs1hMwhiBpnmRmaws3VifqVD3iQY3AK9lj14+ljMFlaBtZ4NA07BNjS7CF27CC0uQmcXoWsXQWy0odoZxC4Cj0EmVfmLbCCnJVuEfD/wFqHsK7T4iga70mmvkHgMLR5Di8fIT/e3DpUlF9aiaavZ4g6iLusSi9GV49C149DiOHSx' \
			b'lyjRHd5LJI6joLmRxexyffkbzeUbDeX4rQR43QHqdQeQdQfI6w5QrzuQKttQeRBedwAxEf7EH8hpiR+J/cB+JK8+cEnJj8jiA8jiA8jiQ36u70fKe+OupMu2zJVUSxBQL0GALEFAXoJoaQ67ElmCKGhuZBhjy8+2sg2sjxvzwJ/fhSPh9Qd+v6RwJPK6iZMh' \
			b't5P3QCgxWQmhltwJVSfXjKvdiWN34sSXyPdZ+ZQNJUJ2Ja4f2JW47EpcZydMSPgzQsHE4rm+EynLRLgQ0eEdqF2uZf7DVf7D1f7Dif9wnZlE6KgOuxAnLiSTHbAUiyd6K0sMJqLBINQG7GaXi9ffk8XYPTkVywsUtl6gsLJAYfMCha0XKEiLbShthbPxEXVo' \
			b'5YvCfBp2KmUxqTCqirxGwSWJsVhZorCyRGFliSI/1zOWqsxRp5KzLbEWWy1U2HqhQideIMkuFtPSHTQXK4sVBd2NHEvzIxiIYxsJR2QmvJJh65UMKysZNq9k2Holw5ocKjPhlQwrKxl0IjMxy83E9AObSV7P4JKSmchyhpXlDCvLGfm5vpmUZY6bSZfNJTGd' \
			b'0OoZS7W0YeuljVYRSQHJVhLxYVuR1Y2C+Ca2gqTn7W6QylrEVBbezSHDWDaB1dQv4Ay9fbN698b4SzejL9wsAS6DtgRqvRNj6LXbFqvLXqyZrp5bJfj1354Ze3VmvX0T/KXz8Zdm+u/Olq/MLIEQ4aeEzYS/Y7QXXIT9QWO2Ah4udaCHYIL36Uvi1KnrIENv' \
			b'ubljgE7jD4ce3duO2UdQq7IBJGUvYTpUtZ6ijy5z0FZHPsuyt7aHXt6F76ENIjH530nsuy3SLMds0zYJTgk1fg3kfCeoaXaEGi5phRfbHDX2+Ho48aaTswZENL/Eu++Ojjtso/INLYr7kVqVHbUovIPb7KFV8evBBjZBjqknDrZrXlZ+4Gjj5sUl3JidYcfL' \
			b'Sj1vMdwIPfxgvTlxR+3N6s8Sbdje0Mef+JNEi/hRfxmPA/Dmq3xX8wZI2wNJFuzotCGQ4gkBSQuQ4jiQoppfTy9nFwMpWuTbuI9Daj8up9WHya4GTbp4K2wDJ9Wgjq4BEIef0rP2mFFwPVN4yNG11P4h5nQXPq5YgeEQTQKVvgUW6LFvhYN1q9CguWCVPoK4' \
			b'6vOHqID5j9BIFKCgyvyxGwj1V4M9B8P1b36M+qfKPk4PQSuk4eAAcLfRImK4PaWquD2NX+Vr/z8GFuLRYoHDUWDB8gdeUU7L6/SR93Kg8mhY6ajiSF6qP8v9Dceby3RYd7BKw9S1x6ibDUdX4sGQP0gVTRVIg8i1q5ii2w4cNxwejtejb6ohIFZ8WwPrqH89' \
			b'49yZ1guNh80sahuXuisdk4LROEB/lX9xPDf8ze4ZIx6H3Mk0WFW1sFEz96QZcfK5zAl/bn/emVV6vGvVQl9vQWyt7jS026tCXTZ9uH3Kr21r/kYCQXuW9xfxhiDZ7EO7QWlJnr6sEWhVguaYqfuo0zSyrIkTu1OzZoHYXiz+cQlQlYDt2/JCELH8F52C8o/L' \
			b'4Rex5OWHrihsKcvSGugVaMkb2fQXfXdJzoOvuGQ3XLJs8RotH9uw4k/8WZ3mmIIfoyCbyJbTSavr3f4rpIt11/sTL9pP7TtA4oW3X/tdcsM74OL6f8xG3DkbqIFN/piLZh0uUHkVI2Y1L2RJq0Kj6xRqwoezMqvyTRLPKRuxq0uOichyrqlRpz6c3iS4Jddt' \
			b'EO71/rkHtYcg3Js+9+UGUvm8Br/WOiiP41aKtoLavAm03PiZN3jyW1Syl5PEbfdsjkItqEME/sU2ZtyynKIv2H9tR7WHINzblbW9TJKykoekKiQbrVQacRWBemtt6N3qhaZJ2ajHtnhbl0Uu3Bbp3fVL79TBg8jur192rw4eRPZw/bIHdfAgssdrl51GbIcO' \
			b'InuznezjXm0bDYDaIjS2n0Lj1A1LkaHOQgdrP05+A404NR7kpZGV2RYDjd/XyyqqWei9XbtqGnXdQTRzxD1Dmmc4liDKgjSzSENnElpSLf+DiE5rogsUjXI1aZoqzPJclEmqd/yRcfRgzqSpPXwuCJBsmr7w/KHBYGnQTLWUkgNrp5vZjEZmYSBxFGk04XhM' \
			b'gbT+mPwf6zDtTA=='

	_PARSER_TOP = 'expr'

	_GREEK      = r'\\alpha|\\beta|\\gamma|\\delta|\\epsilon|\\zeta|\\eta|\\theta|\\iota|\\kappa|\\lambda|\\mu|\\nu|\\xi|\\omnicron|\\rho|' \
			r'\\sigma|\\tau|\\upsilon|\\phi|\\chi|\\psi|\\omega|\\Gamma|\\Delta|\\Theta|\\Lambda|\\Upsilon|\\Xi|\\Phi|\\Pi|\\Psi|\\Sigma|\\Omega'

	_SPECIAL    =  r'\\partial|\\pi|\\infty'
	_CHAR       = fr'[a-zA-Z]'
	_SHORT      =  r'pi|oo|True|False|undefined'
	_TEXTVAR    =  r'\\text\s*\{\s*(True|False|undefined)\s*\}'
	_ONEVAR     = fr'{_CHAR}|{_GREEK}'
	_DSONEVARSP = fr'(?:(\d)|({_SHORT})|({_CHAR}|{_GREEK}|{_SPECIAL})|{_TEXTVAR})'
	_STR        =  r'\'(?:\\.|[^\'])*\'|"(?:\\.|[^"])*["]'

	_FUNCPYONLY = '|'.join (reversed (sorted ('\\?' if s == '?' else s for s in AST.Func.PY_ONLY))) # special cased function name '?' for regex
	_FUNCPYTEX  = '|'.join (reversed (sorted (AST.Func.PY_AND_TEX)))

	TOKENS      = OrderedDict ([ # order matters
		('IGNORE_CURLY',  r'\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		('TRIGH',         r'\\?(?:(a)(?:rc)?)?((?:sin|cos|tan|csc|sec|cot)h?)|\\operatorname\s*\{(sech|csch)\s*\}'),
		('FUNC',         fr'({_FUNCPYONLY})|\\?({_FUNCPYTEX})|\\operatorname\s*\{{\s*({_CHAR}\w*)\s*\}}|\$({_CHAR}\w*)'),
		('SQRT',          r'\\?sqrt'),
		('LOG',           r'\\?log'),
		('LIM',           r'\\lim'),
		('SUM',           r'\\sum'),
		('INT',           r'\\int(?:\s*\\limits)?'),
		('LEFT',          r'\\left'),
		('RIGHT',         r'\\right'),
		('CDOT',          r'\\cdot'),
		('TO',            r'\\to'),
		('FRAC2',        fr'\\frac\s*{_DSONEVARSP}\s*{_DSONEVARSP}'),
		('FRAC1',        fr'\\frac\s*{_DSONEVARSP}'),
		('FRAC',          r'\\frac'),
		('NUM',           r'(?:(\d*\.\d+)|(\d+)\.?)([eE][+-]?\d+)?'),
		# ('VAR',          fr"(?<!\d|{_CHAR}|['])_|({_SHORT})|(d|\\partial\s?)?({_ONEVAR})|{_SPECIAL}|{_TEXTVAR}"),
		('VAR',          fr"({_SHORT})|(d|\\partial\s?)?({_ONEVAR})|{_SPECIAL}|{_TEXTVAR}"),
		('STR',          fr"(?<!\d|{_CHAR}|['}}])({_STR})|\\text\s*\{{\s*({_STR})\s*\}}"),
		('SUB1',         fr'_{_DSONEVARSP}'),
		('SUB',           r'_'),
		('CARET1',       fr'\^{_DSONEVARSP}'),
		('CARET',         r'\^'),
		('DOUBLESTAR',    r'\*\*'),
		('PRIMES',        r"'+"),
		('PARENL',        r'\('),
		('PARENR',        r'\)'),
		('CURLYL',        r'\{'),
		('CURLYR',        r'\}'),
		('BRACKETL',      r'\['),
		('BRACKETR',      r'\]'),
		('BAR',           r'\|'),
		('PLUS',          r'\+'),
		('MINUS',         r'\-'),
		('STAR',          r'\*'),
		('INEQ',          r'==|!=|\\neq?|<=|\\le|<|>=|\\ge|>'),
		('EQ',            r'='),
		('DIVIDE',        r'/'),
		('FACTORIAL',     r'!'),
		('COMMA',         r','),
		('ignore',        r'\\,|\\:|\\?\s+'),
	])

	_FUNC_AST_REMAP = {
		'Abs'       : lambda expr: _expr_func (1, '|', expr.strip_paren ()),
		'Derivative': lambda expr: _expr_func_remap (remap_func_diff, expr),
		'Integral'  : lambda expr: _expr_func_remap (remap_func_intg, expr),
		'Limit'     : lambda expr: _expr_func_remap (remap_func_lim, expr),
		'Sum'       : lambda expr: _expr_func_remap (remap_func_sum, expr),
		'abs'       : lambda expr: _expr_func (1, '|', expr.strip_paren ()),
		'exp'       : lambda expr: _expr_func (2, '^', ('@', 'e'), expr.strip_paren ()),
		'factorial' : lambda expr: _expr_func (1, '!', expr.strip_paren ()),
		'ln'        : lambda expr: _expr_func (1, 'log', expr.strip_paren ()),
	}

	def expr_comma_1    (self, expr_comma, COMMA, expr):                     return AST.flatcat (',', expr_comma, expr)
	def expr_comma_2    (self, expr):                                        return expr

	def expr            (self, expr_eq):                      	             return expr_eq

	def expr_eq_1       (self, expr_ineq1, EQ, expr_ineq2):                  return AST ('=', '=', expr_ineq1, expr_ineq2)
	def expr_eq_2       (self, expr_ineq):                                   return expr_ineq
	def expr_ineq_2     (self, expr_add1, INEQ, expr_add2):                  return AST ('=', AST.Eq.LONG2SHORT.get (INEQ.text, INEQ.text), expr_add1, expr_add2)
	def expr_ineq_3     (self, expr_add):                                    return expr_add

	def expr_add_1      (self, expr_add, PLUS, expr_mul_exp):                return AST.flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2      (self, expr_add, MINUS, expr_mul_exp):               return AST.flatcat ('+', expr_add, expr_mul_exp.neg (stack = True))
	def expr_add_3      (self, expr_mul_exp):                                return expr_mul_exp

	def expr_mul_exp_1  (self, expr_mul_exp, CDOT, expr_neg):                return AST.flatcat ('*', expr_mul_exp, expr_neg)
	def expr_mul_exp_2  (self, expr_mul_exp, STAR, expr_neg):                return AST.flatcat ('*', expr_mul_exp, expr_neg)
	def expr_mul_exp_3  (self, expr_neg):                                    return expr_neg

	def expr_neg_1      (self, MINUS, expr_diff):                            return expr_diff.neg (stack = True)
	def expr_neg_2      (self, expr_diff):                                   return expr_diff

	def expr_diff       (self, expr_div):                                    return _expr_diff (expr_div)

	def expr_div_1      (self, expr_div, DIVIDE, expr_mul_imp):              return AST ('/', expr_div, expr_mul_imp)
	def expr_div_2      (self, expr_div, DIVIDE, MINUS, expr_mul_imp):       return AST ('/', expr_div, expr_mul_imp.neg (stack = True))
	def expr_div_3      (self, expr_mul_imp):                                return expr_mul_imp

	def expr_mul_imp_1  (self, expr_mul_imp, expr_int):                      return AST.flatcat ('*', expr_mul_imp, expr_int)
	def expr_mul_imp_2  (self, expr_int):                                    return expr_int

	def expr_int_1      (self, INT, expr_sub, expr_super, expr_add):         return _expr_int (expr_add, (expr_sub, expr_super))
	def expr_int_2      (self, INT, expr_add):                               return _expr_int (expr_add)
	def expr_int_3      (self, expr_lim):                                    return expr_lim

	def expr_lim_1      (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                              return AST ('lim', expr_neg, expr_var, expr)
	def expr_lim_2      (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_doublestar, PLUS, CURLYR, expr_neg):   return AST ('lim', expr_neg, expr_var, expr, '+')
	def expr_lim_3      (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_doublestar, MINUS, CURLYR, expr_neg):  return AST ('lim', expr_neg, expr_var, expr, '-')
	def expr_lim_6      (self, expr_sum):                                                                            return expr_sum

	def expr_sum_1      (self, SUM, SUB, CURLYL, expr_var, EQ, expr, CURLYR, expr_super, expr_neg):                  return AST ('sum', expr_neg, expr_var, expr, expr_super)
	def expr_sum_2      (self, expr_func):                                                                           return expr_func

	def expr_func_1     (self, SQRT, expr_func_neg):                            return _expr_func (1, 'sqrt', expr_func_neg)
	def expr_func_2     (self, SQRT, BRACKETL, expr, BRACKETR, expr_func_neg):  return _expr_func (1, 'sqrt', expr_func_neg, expr)
	def expr_func_3     (self, LOG, expr_func_neg):                             return _expr_func (1, 'log', expr_func_neg)
	def expr_func_4     (self, LOG, expr_sub, expr_func_neg):                   return _expr_func (1, 'log', expr_func_neg, expr_sub)
	def expr_func_5     (self, TRIGH, expr_func_neg):                           return _expr_func (2, 'func', f'{"a" if TRIGH.grp [0] else ""}{TRIGH.grp [1] or TRIGH.grp [2]}', expr_func_neg)
	def expr_func_6     (self, TRIGH, expr_super, expr_func_neg):
		return \
				AST ('^', _expr_func (2, 'func', f'{TRIGH.grp [0] or ""}{TRIGH.grp [1] or TRIGH.grp [2]}', expr_func_neg), expr_super) \
				if expr_super != AST.NegOne else \
				_expr_func (2, 'func', TRIGH.grp [1] or TRIGH.grp [2], expr_func_neg) \
				if TRIGH.grp [0] else \
				_expr_func (2, 'func', f'a{TRIGH.grp [1] or TRIGH.grp [2]}', expr_func_neg)

	def expr_func_7     (self, FUNC, expr_func_neg):
		func  = FUNC.grp [0] or FUNC.grp [1] or FUNC.grp [2] or FUNC.grp [3] or FUNC.text
		remap = self._FUNC_AST_REMAP.get (func)

		return remap (expr_func_neg) if remap else _expr_func (2, 'func', func, expr_func_neg)

	def expr_func_8     (self, expr_fact):                                   return expr_fact

	def expr_func_neg_1 (self, expr_func):                                   return expr_func
	def expr_func_neg_2 (self, MINUS, expr_func):                            return expr_func.neg (stack = True)

	def expr_fact_1     (self, expr_fact, FACTORIAL):                        return AST ('!', expr_fact)
	def expr_fact_2     (self, expr_pow):                                    return expr_pow

	def expr_pow_1      (self, expr_pow, expr_super):                        return AST ('^', expr_pow, expr_super)
	def expr_pow_2      (self, expr_abs):                                    return expr_abs

	def expr_abs_1      (self, LEFT, BAR1, expr, RIGHT, BAR2):               return AST ('|', expr)
	def expr_abs_2      (self, BAR1, expr, BAR2):                            return AST ('|', expr)
	def expr_abs_3      (self, expr_paren):                                  return expr_paren

	def expr_paren_1    (self, PARENL, expr_comma, PARENR):                  return AST ('(', expr_comma)
	def expr_paren_2    (self, LEFT, PARENL, expr_comma, RIGHT, PARENR):     return AST ('(', expr_comma)
	def expr_paren_3    (self, IGNORE_CURLY, CURLYL, expr, CURLYR):          return expr
	def expr_paren_4    (self, expr_frac):                                   return expr_frac

	def expr_frac_1     (self, FRAC, expr_term1, expr_term2):                return AST ('/', expr_term1, expr_term2)
	def expr_frac_2     (self, FRAC1, expr_term):                            return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_term)
	def expr_frac_3     (self, FRAC2):                                       return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 4))
	def expr_frac_4     (self, expr_term):                                   return expr_term

	def expr_term_1     (self, CURLYL, expr, CURLYR):                        return expr
	def expr_term_2     (self, STR):                                         return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1]))
	def expr_term_3     (self, SUB):                                         return AST ('@', '_')
	def expr_term_4     (self, expr_var):                                    return expr_var
	def expr_term_5     (self, expr_num):                                    return expr_num

	def expr_num        (self, NUM):                                         return AST ('#', NUM.text) if NUM.grp [0] or NUM.grp [2] else AST ('#', NUM.grp [1])

	def expr_var_1      (self, var, PRIMES, subvar):                         return AST ('@', f'{var}{subvar}{PRIMES.text}')
	def expr_var_2      (self, var, subvar, PRIMES):                         return AST ('@', f'{var}{subvar}{PRIMES.text}')
	def expr_var_3      (self, var, PRIMES):                                 return AST ('@', f'{var}{PRIMES.text}')
	def expr_var_4      (self, var, subvar):                                 return AST ('@', f'{var}{subvar}')
	def expr_var_5      (self, var):                                         return AST ('@', var)

	def var             (self, VAR):
		return \
				f'\\partial {VAR.grp [2]}' \
				if VAR.grp [1] and VAR.grp [1] != 'd' else \
				AST.Var.SHORT2LONG.get (VAR.grp [0] or VAR.grp [3], VAR.text)

	def subvar_1        (self, SUB, CURLYL, expr_var, CURLYR):               return f'_{expr_var.var}' if expr_var.var and expr_var.is_single_var else f'_{{{expr_var.var}}}'
	def subvar_2        (self, SUB, CURLYL, NUM, CURLYR):                    return f'_{{{NUM.text}}}'
	def subvar_3        (self, SUB, CURLYL, NUM, subvar, CURLYR):            return f'_{{{NUM.text}{subvar}}}'
	def subvar_4        (self, SUB1):                                        return f'_{AST.Var.SHORT2LONG.get (SUB1.grp [1] or SUB1.grp [3], SUB1.text [1:])}'

	def expr_sub_1      (self, SUB, expr_frac):                              return expr_frac
	def expr_sub_2      (self, SUB1):                                        return _ast_from_tok_digit_or_var (SUB1)

	def expr_super_1    (self, DOUBLESTAR, expr_func):                       return expr_func
	def expr_super_2    (self, DOUBLESTAR, MINUS, expr_func):                return expr_func.neg (stack = True)
	def expr_super_3    (self, CARET, expr_frac):                            return expr_frac
	def expr_super_4    (self, CARET1):                                      return _ast_from_tok_digit_or_var (CARET1)

	def caret_or_doublestar_1 (self, DOUBLESTAR):                            return '**'
	def caret_or_doublestar_2 (self, CARET):                                 return '^'

	#...............................................................................................
	_AUTOCOMPLETE_SUBSTITUTE = { # autocomplete means autocomplete AST tree so it can be rendered, not expression
		'CARET1'             : 'CARET',
		'SUB1'               : 'SUB',
		'FRAC2'              : 'FRAC',
		'FRAC1'              : 'FRAC',
		'expr_sub'           : 'SUB',
		'expr_super'         : 'CARET',
		'caret_or_doublestar': 'CARET',
	}

	_AUTOCOMPLETE_CLOSE = {
		'RIGHT'   : '\\right',
		'PARENR'  : ')',
		'CURLYR'  : '}',
		'BRACKETR': ']',
		'BAR'     : '|',
	}

	def _mark_error (self):
		self.autocompleting = False

		if self.erridx is None:
			self.erridx = self.tokens [self.tokidx - 1].pos

	def _insert_symbol (self, sym):
		if sym in self.TOKENS:
			self.tokens.insert (self.tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, sym), '', self.tok.pos))

			if self.autocompleting and sym in self._AUTOCOMPLETE_CLOSE:
				self.autocomplete.append (self._AUTOCOMPLETE_CLOSE [sym])
			else:
				self.autocompleting = False

		else:
			self.tokens.insert (self.tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, 'VAR'), '', self.tok.pos, (None, None, '', None)))
			self._mark_error ()

		return True

	def _parse_autocomplete_expr_comma (self, rule):
		idx = -1 -len (rule [1])

		if self.stack [idx] [1] == 'CURLYL':
			return self._insert_symbol ('CURLYR')

		if self.stack [idx] [1] != 'PARENL':
			return False

		if self.stack [idx - 1] [1] == 'LEFT':
			return self._insert_symbol ('RIGHT')

		return self._insert_symbol ('PARENR')

	def _parse_autocomplete_expr_int (self):
		s               = self.stack [-1]
		self.stack [-1] = (s [0], s [1], AST ('*', (s [2], AST.VarNull)))
		expr_vars       = set ()
		expr_diffs      = set ()

		if self.autocompleting:
			stack = [s [2]]

			while stack:
				ast = stack.pop ()

				if ast.is_var:
					(expr_diffs if ast.is_differential else expr_vars).add (ast.var)
				else:
					stack.extend (filter (lambda a: isinstance (a, tuple), ast))

		expr_vars  = expr_vars - {'_', 'e', 'i'} - set (AST.Var.LONG2SHORT)
		expr_vars -= set (var [1:] for var in expr_diffs)

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

		if pos >= len (rule [1]): # special error raised by rule reduction function or end of comma expression
			if rule [0] == 'expr_comma':
				return self._parse_autocomplete_expr_comma (rule)

			if rule [0] == 'expr_int':
				return self._parse_autocomplete_expr_int ()

			return False

		return self._insert_symbol (rule [1] [pos])

	def parse_success (self, reduct):
		self.parse_results.append ((reduct, self.erridx, self.autocomplete))

		return True # continue parsing if conflict branches remain to find best resolution

	def parse (self, text):
		self.parse_results  = [] # [(reduct, erridx, autocomplete), ...]
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
			print ()
			for res in rated:
				print ('parse:', res [-1])

		return next (iter (rated)) [-1]

class sparser: # for single script
	Parser = Parser

# DEBUG!
# if __name__ == '__main__':
# 	p = Parser ()
# 	a = p.parse ('\\left(1,2')
# 	print (a)

# 	print (p.parse ('1') [0])
# 	print (p.parse ('x') [0])
# 	print (p.parse ('x!') [0])
# 	print (p.parse ('|x|') [0])
# 	print (p.parse ('x/y') [0])
# 	print (p.parse ('x/(y/z)') [0])
# 	print (p.parse ('sin x') [0])
# 	print (p.parse ('sin x**2') [0])
# 	print (p.parse ('sin (x**2)') [0])
# 	print (p.parse ('sin (x)**2') [0])
# 	print (p.parse ('x') [0])
# 	print (p.parse ('-x') [0])
# 	print (p.parse ('-{-x}') [0])
# 	print (p.parse ('\\int dx') [0])
# 	print (p.parse ('\\int dx/2') [0])
# 	print (p.parse ('\\int 2 dx') [0])
# 	print (p.parse ('\\int 3 / 2 dx') [0])
# 	print (p.parse ('\\int x + y dx') [0])
# 	print (p.parse ('\\int_0^1 dx') [0])
# 	print (p.parse ('\\int_0^1 dx/2') [0])
# 	print (p.parse ('\\int_0^1 2 dx') [0])
# 	print (p.parse ('\\int_0^1 3 / 2 dx') [0])
# 	print (p.parse ('\\int_0^1 x + y dx') [0])
# 	print (p.parse ('dx') [0])
# 	print (p.parse ('d / dx x') [0])
# 	print (p.parse ('d**2 / dx**2 x') [0])
# 	print (p.parse ('d**2 / dx dy x') [0])
# 	print (p.parse ('\\frac{d}{dx} x') [0])
# 	print (p.parse ('\\frac{d**2}{dx**2} x') [0])
# 	print (p.parse ('\\frac{d**2}{dxdy} x') [0])
# Convert between internal AST and sympy expressions and write out LaTeX, simple and python code

# TODO: native sp.Piecewise: \int_0^\infty e^{-st} dt

import re
import sympy as sp
sp.numbers = sp.numbers # medication for pylint
sp.boolalg = sp.boolalg


_SYMPY_FLOAT_PRECISION = None

_rec_num_deconstructed = re.compile (r'^(-?)(\d*[^0.e])?(0*)(?:(\.)(0*)(\d*[^0e])?(0*))?(?:([eE])([+-]?\d+))?$') # -101000.000101000e+123 -> (-) (101) (000) (.) (000) (101) (000) (e) (+123)

#...............................................................................................
class AST_Unknown: # for displaying elements we do not know how to handle, only returned from SymPy processing, not passed in
	op = '???'

	def __init__ (self, tex, py):
		self.tex, self.py = tex, py

def _ast_is_neg (ast):
	return \
			ast.is_minus or \
			ast.is_num and ast.num [0] == '-' or \
			ast.is_mul and _ast_is_neg (ast.muls [0])

def set_precision (ast): # recurse through ast to set sympy float precision according to largest string of digits found
	global _SYMPY_FLOAT_PRECISION

	prec  = 15
	stack = [ast]

	while stack:
		ast = stack.pop ()

		if not isinstance (ast, AST):
			pass # nop
		elif ast.is_num:
			prec = max (prec, len (ast.num))
		else:
			stack.extend (ast [1:])

	_SYMPY_FLOAT_PRECISION = prec if prec > 15 else None

#...............................................................................................
def ast2tex (ast): # abstract syntax tree -> LaTeX text
	return _ast2tex_funcs [ast.op] (ast)

def _ast2tex_curly (ast):
	return f'{ast2tex (ast)}' if ast.is_single_unit else f'{{{ast2tex (ast)}}}'

def _ast2tex_paren (ast):
	return ast2tex (ast) if ast.is_paren else f'\\left({ast2tex (ast)} \\right)'

def _ast2tex_paren_mul_exp (ast, ret_has = False, also = {'+'}):
	if ast.is_mul:
		s, has = _ast2tex_mul (ast, True)
	else:
		s, has = ast2tex (ast), ast.op in also

	s = f'\\left({s} \\right)' if has else s

	return (s, has) if ret_has else s

def _ast2tex_num (ast):
	m, e = ast.mant_and_exp ()

	return m if e is None else f'{m} \\cdot 10^{_ast2tex_curly (AST ("#", e))}'

def _ast2tex_mul (ast, ret_has = False):
	t   = []
	p   = None
	has = False

	for n in ast.muls:
		s = f'{_ast2tex_paren (n) if n.is_add or (p and _ast_is_neg (n)) else ast2tex (n)}'

		if p and (n.op in {'!', '#'} or n.is_null_var or p.op in {'lim', 'sum', 'intg'} or \
				(n.is_pow and n.base.is_pos_num) or (n.op in {'/', 'diff'} and p.op in {'#', '/', 'diff'})):
			t.append (f' \\cdot {s}')
			has = True

		elif p and (p.is_diff_or_part_solo or p.op in {'sqrt'} or n.is_diff_or_part or p.is_diff_or_part):
			t.append (f'\\ {s}')
		else:
			t.append (f'{"" if not p else " "}{s}')

		p = n

	return (''.join (t), has) if ret_has else ''.join (t)

def _ast2tex_pow (ast):
	b = ast2tex (ast.base)
	p = _ast2tex_curly (ast.exp)

	if ast.base.is_trigh_func_noninv_func and ast.exp.is_single_unit:
		i = len (ast.base.func) + (15 if ast.base.func in {'sech', 'csch'} else 1)

		return f'{b [:i]}^{p}{b [i:]}'

	if ast.base.op in {'(', '|', '@'} or ast.base.is_pos_num:
		return f'{b}^{p}'

	return f'\\left({b} \\right)^{p}'

def _ast2tex_log (ast):
	return \
			f'\\log{_ast2tex_paren (ast.log)}' \
			if ast.base is None else \
			f'\\log_{_ast2tex_curly (ast.base)}{_ast2tex_paren (ast.log)}'

def _ast2tex_func (ast):
	if ast.is_trigh_func:
		n = (f'\\operatorname{{{ast.func [1:]}}}^{{-1}}' \
				if ast.func in {'asech', 'acsch'} else \
				f'\\{ast.func [1:]}^{{-1}}') \
				if ast.func [0] == 'a' else \
				(f'\\operatorname{{{ast.func}}}' if ast.func in {'sech', 'csch'} else f'\\{ast.func}')

		return f'{n}{_ast2tex_paren (ast.arg)}'

	return \
			f'\\{ast.func}{_ast2tex_paren (ast.arg)}' \
			if ast.func in AST.Func.PY_AND_TEX else \
			f'\\operatorname{{{ast.func}}}{_ast2tex_paren (ast.arg)}'

def _ast2tex_lim (ast):
	s = ast2tex (ast.to) if ast.dir is None else (ast2tex (AST ('^', ast.to, AST.Zero)) [:-1] + ast.dir)

	return f'\\lim_{{{ast2tex (ast.lvar)} \\to {s}}} {_ast2tex_paren_mul_exp (ast.lim)}'

def _ast2tex_sum (ast):
	return f'\\sum_{{{ast2tex (ast.svar)} = {ast2tex (ast.from_)}}}^{_ast2tex_curly (ast.to)} {_ast2tex_paren_mul_exp (ast.sum)}' \

_rec_diff_var_single_start = re.compile (r'^d(?=[^_])')

def _ast2tex_diff (ast):
	ds = set ()
	p  = 0

	for n in ast.dvs:
		if n.is_var:
			p += 1

			if n.var:
				ds.add (n.var)

		else: # n = ('^', ('@', 'diff or part'), ('#', 'int'))
			p += int (n.exp.num)
			ds.add (n.base.var)

	if not ds:
		return f'\\frac{{d}}{{}}{_ast2tex_paren (ast.diff)}'

	if len (ds) == 1 and ds.pop () [0] != '\\': # is not '\\partial'
		return f'\\frac{{d{"" if p == 1 else f"^{p}"}}}{{{"".join (ast2tex (n) for n in ast.dvs)}}}{_ast2tex_paren (ast.diff)}'

	else:
		s = ''.join (_rec_diff_var_single_start.sub ('\\partial ', ast2tex (n)) for n in ast.dvs)

		return f'\\frac{{\\partial{"" if p == 1 else f"^{p}"}}}{{{s}}}{_ast2tex_paren (ast.diff)}'

def _ast2tex_intg (ast):
	if ast.from_ is None:
		return \
				f'\\int \\ {ast2tex (ast.dv)}' \
				if ast.intg is None else \
				f'\\int {ast2tex (ast.intg)} \\ {ast2tex (ast.dv)}'
	else:
		return \
				f'\\int_{_ast2tex_curly (ast.from_)}^{_ast2tex_curly (ast.to)} \\ {ast2tex (ast.dv)}' \
				if ast.intg is None else \
				f'\\int_{_ast2tex_curly (ast.from_)}^{_ast2tex_curly (ast.to)} {ast2tex (ast.intg)} \\ {ast2tex (ast.dv)}'

_ast2tex_funcs = {
	'=': lambda ast: f'{ast2tex (ast.lhs)} {AST.Eq.SHORT2LONG.get (ast.rel, ast.rel)} {ast2tex (ast.rhs)}',
	'#': _ast2tex_num,
	'@': lambda ast: str (ast.var) if ast.var else '{}',
	'"': lambda ast: f'\\text{{{repr (ast.str_)}}}',
	',': lambda ast: ','.join (ast2tex (parm) for parm in ast.commas),
	'(': lambda ast: f'\\left({ast2tex (ast.paren)} \\right)',
	'|': lambda ast: f'\\left|{ast2tex (ast.abs)} \\right|',
	'-': lambda ast: f'-{_ast2tex_paren (ast.minus)}' if ast.minus.is_add else f'-{ast2tex (ast.minus)}',
	'!': lambda ast: f'{_ast2tex_paren (ast.fact)}!' if (ast.fact.op not in {'#', '@', '(', '|', '!', '^'} or ast.fact.is_neg_num) else f'{ast2tex (ast.fact)}!',
	'+': lambda ast: ' + '.join (ast2tex (n) for n in ast.adds).replace (' + -', ' - '),
	'*': _ast2tex_mul,
	'/': lambda ast: f'\\frac{{{ast2tex (ast.numer)}}}{{{ast2tex (ast.denom)}}}',
	'^': _ast2tex_pow,
	'log': _ast2tex_log,
	'sqrt': lambda ast: f'\\sqrt{{{ast2tex (ast.rad.strip_paren (1))}}}' if ast.idx is None else f'\\sqrt[{ast2tex (ast.idx)}]{{{ast2tex (ast.rad.strip_paren (1))}}}',
	'func': _ast2tex_func,
	'lim': _ast2tex_lim,
	'sum': _ast2tex_sum,
	'diff': _ast2tex_diff,
	'intg': _ast2tex_intg,
	'???': lambda ast: ast.tex,
}

#...............................................................................................
def ast2simple (ast): # abstract syntax tree -> simple text
	return _ast2simple_funcs [ast.op] (ast)

def _ast2simple_curly (ast):
	return f'{ast2simple (ast)}' if ast.is_single_unit else f'{{{ast2simple (ast)}}}'

def _ast2simple_paren (ast):
	return ast2simple (ast) if ast.is_paren else f'({ast2simple (ast)})'

def _ast2simple_paren_mul_exp (ast, ret_has = False, also = {'+'}):
	if ast.is_mul:
		s, has = _ast2simple_mul (ast, True)
	else:
		s, has = ast2simple (ast), ast.op in also

	s = f'({s})' if has else s

	return (s, has) if ret_has else s

def _ast2simple_mul (ast, ret_has = False):
	t   = []
	p   = None
	has = False

	for n in ast.muls:
		s = f'{_ast2simple_paren (n) if n.is_add or (p and _ast_is_neg (n)) else ast2simple (n)}'

		if p and (n.op in {'!', '#', 'lim', 'sum', 'intg'} or n.is_null_var or \
				(n.is_pow and n.base.is_pos_num) or n.op in {'/', 'diff'} or p.op in {'/', 'diff'}):
			t.append (f' * {ast2simple (n)}')
			has = True

		elif p and (p.is_diff_or_part_solo or \
				(n.op not in {'#', '@', '(', '|', '^'} or p.op not in {'#', '@', '(', '|', '^'}) or \
				n.has_short_var or p.has_short_var or n.is_diff_or_part or p.is_diff_or_part):
			t.append (f' {s}')

		else:
			t.append (s)

		p = n

	return (''.join (t), has) if ret_has else ''.join (t)

def _ast2simple_div (ast):
	n, ns = _ast2simple_paren_mul_exp (ast.numer, True, {'+', '/', 'lim', 'sum', 'diff'})
	d, ds = _ast2simple_paren_mul_exp (ast.denom, True, {'+', '/', 'lim', 'sum', 'diff'})
	s     = ns or ds or ast.numer.strip_minus ().op not in {'#', '@', '*'} or ast.denom.strip_minus ().op not in {'#', '@', '*'}

	return f'{n}{" / " if s else "/"}{d}'

def _ast2simple_pow (ast):
	b = ast2simple (ast.base)
	p = f'{_ast2simple_paren (ast.exp)}' if ast.exp.strip_minus ().op in {'+', '*', '/', 'lim', 'sum', 'diff', 'intg'} else ast2simple (ast.exp)

	if ast.base.is_trigh_func_noninv_func and ast.exp.is_single_unit:
		i = len (ast.base.func)

		return f'{b [:i]}^{p}{b [i:]}'

	if ast.base.op in {'@', '(', '|'} or ast.base.is_pos_num:
		return f'{b}**{p}'

	return f'({b})**{p}'

def _ast2simple_log (ast):
	return \
			f'log{_ast2simple_paren (ast.log)}' \
			if ast.base is None else \
			f'log_{_ast2simple_curly (ast.base)}{_ast2simple_paren (ast.log)}'

def _ast2simple_func (ast):
	if ast.is_trigh_func:
		return f'{ast.func}{_ast2simple_paren (ast.arg)}'

	return \
			f'{ast.func}{_ast2simple_paren (ast.arg)}' \
			if ast.func in AST.Func.PY_ALL else \
			f'${ast.func}{_ast2simple_paren (ast.arg)}'

def _ast2simple_lim (ast):
	s = ast2simple (ast.to) if ast.dir is None else ast2simple (AST ('^', ast [3], AST.Zero)) [:-1] + ast [4]

	return f'\\lim_{{{ast2simple (ast.lvar)} \\to {s}}} {_ast2simple_paren_mul_exp (ast.lim)}'

def _ast2simple_sum (ast):
	return f'\\sum_{{{ast2simple (ast.svar)}={ast2simple (ast.from_)}}}^{_ast2simple_curly (ast.to)} {_ast2simple_paren_mul_exp (ast.sum)}' \

_ast2simple_diff_single_rec = re.compile ('^d')

def _ast2simple_diff (ast):
	p = 0

	for n in ast.dvs:
		if n.is_var:
			d  = n.diff_or_part_start_text ()
			p += 1
		else: # n = ('^', ('@', 'differential'), ('#', 'int'))
			d  = n.base.diff_or_part_start_text ()
			p += int (n.exp.num)

	return f'{d}{"" if p == 1 else f"^{p}"}/{"".join (ast2simple (n) for n in ast.dvs)}{_ast2simple_paren (ast.diff)}'

def _ast2simple_intg (ast):
	if ast.from_ is None:
		return \
				f'\\int {ast2simple (ast.dv)}' \
				if ast.intg is None else \
				f'\\int {ast2simple (ast.intg)} {ast2simple (ast.dv)}'
	else:
		return \
				f'\\int_{_ast2simple_curly (ast.from_)}^{_ast2simple_curly (ast.to)} {ast2simple (ast.dv)}' \
				if ast.intg is None else \
				f'\\int_{_ast2simple_curly (ast.from_)}^{_ast2simple_curly (ast.to)} {ast2simple (ast.intg)} {ast2simple (ast.dv)}'

_ast2simple_funcs = {
	'=': lambda ast: f'{ast2simple (ast.lhs)} {ast.rel} {ast2simple (ast.rhs)}',
	'#': lambda ast: ast.num,
	'@': lambda ast: ast.as_short_var_text (),
	'"': lambda ast: repr (ast.str_),
	',': lambda ast: ','.join (ast2simple (parm) for parm in ast.commas),
	'(': lambda ast: f'({ast2simple (ast.paren)})',
	'|': lambda ast: f'|{ast2simple (ast.abs)}|',
	'-': lambda ast: f'-{_ast2simple_paren (ast.minus)}' if ast.minus.is_add else f'-{ast2simple (ast.minus)}',
	'!': lambda ast: f'{_ast2simple_paren (ast.fact)}!' if (ast.fact.op not in {'#', '@', '(', '|', '!', '^'} or ast.fact.is_neg_num) else f'{ast2simple (ast.fact)}!',
	'+': lambda ast: ' + '.join (ast2simple (n) for n in ast.adds).replace (' + -', ' - '),
	'*': _ast2simple_mul,
	'/': _ast2simple_div,
	'^': _ast2simple_pow,
	'log': _ast2simple_log,
	'sqrt': lambda ast: f'\\sqrt{{{ast2simple (ast.rad.strip_paren (1))}}}' if ast.idx is None else f'\\sqrt[{ast2simple (ast.idx)}]{{{ast2simple (ast.rad.strip_paren (1))}}}',
	'func': _ast2simple_func,
	'lim': _ast2simple_lim,
	'sum': _ast2simple_sum,
	'diff': _ast2simple_diff,
	'intg': _ast2simple_intg,
	'???': lambda ast: 'undefined',
}

#...............................................................................................
def ast2py (ast): # abstract syntax tree -> python code text
	return _ast2py_funcs [ast.op] (ast)

def _ast2py_curly (ast):
	return \
			_ast2py_paren (ast) \
			if ast.strip_minus ().op in {'+', '*', '/'} or ast.is_neg_num or (ast.is_log and ast.base is not None) else \
			ast2py (ast)

def _ast2py_paren (ast):
	return ast2py (ast) if ast.is_paren else f'({ast2py (ast)})'

def _ast2py_div (ast):
	n = _ast2py_curly (ast.numer)
	d = _ast2py_curly (ast.denom)

	return f'{n}{" / " if ast.numer.strip_minus ().op not in {"#", "@"} or ast.denom.strip_minus ().op not in {"#", "@"} else "/"}{d}'

def _ast2py_pow (ast):
	b = _ast2py_curly (ast.base)
	e = _ast2py_curly (ast.exp)

	return f'{b}**{e}'

def _ast2py_log (ast):
	return \
			f'log{_ast2py_paren (ast.log)}' \
			if ast.base is None else \
			f'log{_ast2py_paren (ast.log)} / log{_ast2py_paren (ast.base)}' \

def _ast2py_lim (ast):
	return \
		f'''Limit({ast2py (ast.lim)}, {ast2py (ast.lvar)}, {ast2py (ast.to)}''' \
		f'''{", dir='+-'" if ast.dir is None else ", dir='-'" if ast.dir == '-' else ""})'''

def _ast2py_diff (ast):
	args = sum ((
			(ast2py (n.as_var ()),) \
			if n.is_var else \
			(ast2py (n.base.as_var ()), str (n.exp.num)) \
			for n in ast.dvs \
			), ())

	return f'Derivative({ast2py (ast.diff)}, {", ".join (args)})'

def _ast2py_intg (ast):
	if ast.from_ is None:
		return \
				f'Integral(1, {ast2py (ast.dv.as_var ())})' \
				if ast.intg is None else \
				f'Integral({ast2py (ast.intg)}, {ast2py (ast.dv.as_var ())})'
	else:
		return \
				f'Integral(1, ({ast2py (ast.dv.as_var ())}, {ast2py (ast.from_)}, {ast2py (ast.to)}))' \
				if ast.intg is None else \
				f'Integral({ast2py (ast.intg)}, ({ast2py (ast.dv.as_var ())}, {ast2py (ast.from_)}, {ast2py (ast.to)}))'

_rec_ast2py_varname_sanitize = re.compile (r'\{|\}')

_ast2py_funcs = {
	'=': lambda ast: f'{ast2py (ast.lhs)} {ast.rel} {ast2py (ast.rhs)}',
	'#': lambda ast: ast.num,
	'@': lambda ast: _rec_ast2py_varname_sanitize.sub ('_', ast.as_short_var_text ()).replace ('\\', '').replace ("'", '_prime'),
	'"': lambda ast: repr (ast.str_),
	',': lambda ast: ','.join (ast2py (parm) for parm in ast.commas),
	'(': lambda ast: f'({ast2py (ast.paren)})',
	'|': lambda ast: f'abs({ast2py (ast.abs)})',
	'-': lambda ast: f'-{_ast2py_paren (ast.minus)}' if ast.minus.is_add else f'-{ast2py (ast.minus)}',
	'!': lambda ast: f'factorial({ast2py (ast.fact)})',
	'+': lambda ast: ' + '.join (ast2py (n) for n in ast.adds).replace (' + -', ' - '),
	'*': lambda ast: '*'.join (_ast2py_paren (n) if n.is_add else ast2py (n) for n in ast.muls),
	'/': _ast2py_div,
	'^': _ast2py_pow,
	'log': _ast2py_log,
	'sqrt': lambda ast: f'sqrt{_ast2py_paren (ast.rad.strip_paren (1))}' if ast.idx is None else ast2py (AST ('^', ast.rad.strip_paren (1), ('/', AST.One, ast.idx))),
	'func': lambda ast: f'{AST.Func.ALIAS.get (ast.func, ast.func)}{_ast2py_paren (ast.arg)}',
	'lim': _ast2py_lim,
	'sum': lambda ast: f'Sum({ast2py (ast.sum)}, ({ast2py (ast.svar)}, {ast2py (ast.from_)}, {ast2py (ast.to)}))',
	'diff': _ast2py_diff,
	'intg': _ast2py_intg,
	'???': lambda ast: ast.py,
}

#...............................................................................................
def ast2spt (ast, doit = False): # abstract syntax tree -> sympy tree (expression)
	spt = _ast2spt_funcs [ast.op] (ast)

	if doit:
		if spt.__class__ != sp.Piecewise: # in {sp.Limit, sp.Sum, sp.Derivative, sp.Integral}:
			spt = spt.doit ()

	return spt

def _ast2spt_func (ast):
	f = getattr (sp, AST.Func.ALIAS.get (ast.func, ast.func))
	p = ast2spt (ast.arg)

	return f (*p) if isinstance (p, tuple) else f (p)

def _ast2spt_diff (ast):
	args = sum ((
			(ast2spt (n.as_var ()),) \
			if n.is_var else \
			(ast2spt (n.base.as_var ()), sp.Integer (n.exp.num)) \
			for n in ast.dvs \
			), ())

	return sp.Derivative (ast2spt (ast [1]), *args)

def _ast2spt_intg (ast):
	if ast.from_ is None:
		return \
				sp.Integral (1, ast2spt (ast.dv.as_var ())) \
				if ast.intg is None else \
				sp.Integral (ast2spt (ast.intg), ast2spt (ast.dv.as_var ()))
	else:
		return \
				sp.Integral (1, (ast2spt (ast.dv.as_var ()), ast2spt (ast.from_), ast2spt (ast.to))) \
				if ast.intg is None else \
				sp.Integral (ast2spt (ast [1]), (ast2spt (ast.dv.as_var ()), ast2spt (ast.from_), ast2spt (ast.to)))

_ast2spt_eq = {
	'=':  sp.Eq,
	'!=': sp.Ne,
	'<':  sp.Lt,
	'<=': sp.Le,
	'>':  sp.Gt,
	'>=': sp.Ge,
}

_ast2spt_consts = {
	'e'                : sp.E,
	'i'                : sp.I,
	'\\pi'             : sp.pi,
	'\\infty'          : sp.oo,
	'\\text{True}'     : sp.boolalg.true,
	'\\text{False}'    : sp.boolalg.false,
	'\\text{undefined}': sp.nan,
}

_ast2spt_funcs = {
	'=': lambda ast: _ast2spt_eq [ast.rel] (ast2spt (ast.lhs), ast2spt (ast.rhs)),
	'#': lambda ast: sp.Integer (ast [1]) if ast.is_int_text (ast.num) else sp.Float (ast.num, _SYMPY_FLOAT_PRECISION),
	'@': lambda ast: _ast2spt_consts.get (ast.var, sp.Symbol (ast.var)),
	'"': lambda ast: ast.str_,
	',': lambda ast: tuple (ast2spt (p) for p in ast.commas),
	'(': lambda ast: ast2spt (ast.paren),
	'|': lambda ast: sp.Abs (ast2spt (ast.abs)),
	'-': lambda ast: -ast2spt (ast.minus),
	'!': lambda ast: sp.factorial (ast2spt (ast.fact)),
	'+': lambda ast: sp.Add (*(ast2spt (n) for n in ast.adds)),
	'*': lambda ast: sp.Mul (*(ast2spt (n) for n in ast.muls)),
	'/': lambda ast: sp.Mul (ast2spt (ast.numer), sp.Pow (ast2spt (ast.denom), -1)),
	'^': lambda ast: sp.Pow (ast2spt (ast.base), ast2spt (ast.exp)),
	'log': lambda ast: sp.log (ast2spt (ast.log)) if ast.base is None else sp.log (ast2spt (ast.log), ast2spt (ast.base)),
	'sqrt': lambda ast: sp.Pow (ast2spt (ast.rad), sp.Pow (2, -1)) if ast.idx is None else sp.Pow (ast2spt (ast.rad), sp.Pow (ast2spt (ast.idx), -1)),
	'func': _ast2spt_func,
	'lim': lambda ast: (sp.Limit if ast.dir else sp.limit) (ast2spt (ast.lim), ast2spt (ast.lvar), ast2spt (ast.to), dir = ast.dir or '+-'),
	'sum': lambda ast: sp.Sum (ast2spt (ast.sum), (ast2spt (ast.svar), ast2spt (ast.from_), ast2spt (ast.to))),
	'diff': _ast2spt_diff,
	'intg': _ast2spt_intg,
}

#...............................................................................................
def spt2ast (spt): # sympy tree (expression) -> abstract syntax tree
	for cls in spt.__class__.__mro__:
		func = _spt2ast_funcs.get (cls)

		if func:
			return func (spt)

		if cls is sp.Function:
			if len (spt.args) != 1:
				break

			return AST ('func', spt.__class__.__name__, spt2ast (spt.args [0]))

	return AST_Unknown (sp.latex (spt), str (spt))

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

def _spt2ast_add (spt):
	args = spt._sorted_args

	for arg in args:
		if isinstance (arg, sp.Order):
			break
	else:
		args = args [::-1]

	return AST ('+', tuple (spt2ast (arg) for arg in args))

def _spt2ast_mul (spt):
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

def _spt2ast_pow (spt):
	if spt.args [1].is_negative:
		return AST ('/', AST.One, spt2ast (sp.Pow (spt.args [0], -spt.args [1])))

	if spt.args [1] == 0.5:
		return AST ('sqrt', spt2ast (spt.args [0]))

	return AST ('^', spt2ast (spt.args [0]), spt2ast (spt.args [1]))

def _spt2ast_func (spt):
	return AST ('func', spt.__class__.__name__, spt2ast (spt.args [0]))

def _spt2ast_integral (spt):
	return \
			AST ('intg', spt2ast (spt.args [0]), AST ('@', f'd{spt2ast (spt.args [1] [0]) [1]}'), spt2ast (spt.args [1] [1]), spt2ast (spt.args [1] [2])) \
			if len (spt.args [1]) == 3 else \
			AST ('intg', spt2ast (spt.args [0]), AST ('@', f'd{spt2ast (spt.args [1] [0]) [1]}'))

_spt2ast_funcs = {
	tuple: lambda spt: AST ('(', (',', tuple (spt2ast (t) for t in spt))),
	sp.Tuple: lambda spt: spt2ast (spt.args),

	sp.numbers.NaN: lambda spt: AST.Undefined,
	sp.Integer: _spt2ast_num,
	sp.Float: _spt2ast_num,
	sp.Rational: lambda spt: AST ('/', ('#', str (spt.p)), ('#', str (spt.q))) if spt.p >= 0 else AST ('-', ('/', ('#', str (-spt.p)), ('#', str (spt.q)))),
	sp.numbers.ImaginaryUnit: lambda ast: AST.I,
	sp.numbers.Pi: lambda spt: AST.Pi,
	sp.numbers.Exp1: lambda spt: AST.E,
	sp.exp: lambda spt: AST ('^', AST.E, spt2ast (spt.args [0])),
	sp.numbers.Infinity: lambda spt: AST.Infty,
	sp.numbers.NegativeInfinity: lambda spt: AST ('-', AST.Infty),
	sp.numbers.ComplexInfinity: lambda spt: AST.Infty, # not exactly but whatever
	sp.Symbol: lambda spt: AST ('@', spt.name),

	sp.boolalg.BooleanTrue: lambda spt: AST.True_,
	sp.boolalg.BooleanFalse: lambda spt: AST.False_,
	sp.Eq: lambda spt: AST ('=', '=', spt2ast (spt.args [0]), spt2ast (spt.args [1])),
	sp.Ne: lambda spt: AST ('=', '!=', spt2ast (spt.args [0]), spt2ast (spt.args [1])),
	sp.Lt: lambda spt: AST ('=', '<', spt2ast (spt.args [0]), spt2ast (spt.args [1])),
	sp.Le: lambda spt: AST ('=', '<=', spt2ast (spt.args [0]), spt2ast (spt.args [1])),
	sp.Gt: lambda spt: AST ('=', '>', spt2ast (spt.args [0]), spt2ast (spt.args [1])),
	sp.Ge: lambda spt: AST ('=', '>=', spt2ast (spt.args [0]), spt2ast (spt.args [1])),

	sp.Abs: lambda spt: AST ('|', spt2ast (spt.args [0])),
	sp.Add: _spt2ast_add,
	sp.arg: lambda spt: AST ('func', 'arg', spt2ast (spt.args [0])),
	sp.factorial: lambda spt: AST ('!', spt2ast (spt.args [0])),
	sp.log: lambda spt: AST ('log', spt2ast (spt.args [0])) if len (spt.args) == 1 else AST ('log', spt2ast (spt.args [0]), spt2ast (spt.args [1])),
	sp.Mul: _spt2ast_mul,
	sp.Pow: _spt2ast_pow,
	sp.functions.elementary.trigonometric.TrigonometricFunction: _spt2ast_func,
	sp.functions.elementary.hyperbolic.HyperbolicFunction: _spt2ast_func,
	sp.functions.elementary.trigonometric.InverseTrigonometricFunction: _spt2ast_func,
	sp.functions.elementary.hyperbolic.InverseHyperbolicFunction: _spt2ast_func,

	sp.Sum: lambda spt: AST ('sum', spt2ast (spt.args [0]), spt2ast (spt.args [1] [0]), spt2ast (spt.args [1] [1]), spt2ast (spt.args [1] [2])),
	sp.Integral: _spt2ast_integral,

	sp.Order: lambda spt: AST ('func', 'O', spt2ast (spt.args [0]) if spt.args [1] [1] == 0 else spt2ast (spt.args)),
}

#...............................................................................................
class sym: # for single script
	set_precision = set_precision
	ast2tex       = ast2tex
	ast2simple    = ast2simple
	ast2py        = ast2py
	ast2spt       = ast2spt
	spt2ast       = spt2ast

## DEBUG!
# if __name__ == '__main__':
# 	print (_rec_num_deconstructed.match ('10100.0010100').groups ())
# 	t = ast2spt (('intg', ('@', 'dx')))
# 	print (t)

#!/usr/bin/env python
# python 3.6+

# TODO: Exception prevents restart on file date change?

import getopt
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

import sympy as sp


_DEFAULT_ADDRESS          = ('localhost', 8000)


_STATIC_FILES             = {'/style.css': 'css', '/script.js': 'javascript', '/index.html': 'html', '/help.html': 'html'}

#...............................................................................................
_last_ast = AST.Zero # last evaluated expression for _ usage

def _ast_replace (ast, src, dst):
	return \
			ast if not isinstance (ast, AST) else \
			dst if ast == src else \
			AST (*(_ast_replace (s, src, dst) for s in ast))

class Handler (SimpleHTTPRequestHandler):
	def do_GET (self):
		if self.path == '/':
			self.path = '/index.html'

		if self.path not in _STATIC_FILES:
			self.send_error (404, f'Invalid path {self.path!r}')

		elif not _RUNNING_AS_SINGLE_SCRIPT:
			return SimpleHTTPRequestHandler.do_GET (self)

		else:
			self.send_response (200)
			self.send_header ('Content-type', f'text/{_STATIC_FILES [self.path]}')
			self.end_headers ()
			self.wfile.write (_FILES [self.path [1:]])

	def do_POST (self):
		global _last_ast

		request = parse_qs (self.rfile.read (int (self.headers ['Content-Length'])).decode ('utf8'), keep_blank_values = True)
		parser  = sparser.Parser ()

		for key, val in list (request.items ()):
			if len (val) == 1:
				request [key] = val [0]

		if request ['mode'] == 'validate':
			ast, erridx, autocomplete = parser.parse (request ['text'])
			tex = simple = py         = None

			if ast is not None:
				ast    = _ast_replace (ast, ('@', '_'), _last_ast)
				tex    = sym.ast2tex (ast)
				simple = sym.ast2simple (ast)
				py     = sym.ast2py (ast)

				if os.environ.get ('SYMPAD_DEBUG'):
					print ()
					print ('ast:   ', ast)
					print ('tex:   ', tex)
					print ('simple:', simple)
					print ('py:    ', py)
					print ()

			response = {
				'tex'         : tex,
				'simple'      : simple,
				'py'          : py,
				'erridx'      : erridx,
				'autocomplete': autocomplete,
			}

		else: # mode = 'evaluate'
			try:
				ast, _, _ = parser.parse (request ['text'])
				ast       = _ast_replace (ast, ('@', '_'), _last_ast)

				sym.set_precision (ast)

				spt       = sym.ast2spt (ast, doit = True)
				ast       = sym.spt2ast (spt)
				_last_ast = ast

				if os.environ.get ('SYMPAD_DEBUG'):
					print ()
					print ('spt:        ', repr (spt))
					print ('sympy latex:', sp.latex (spt))
					print ()

				response  = {
					'tex'   : sym.ast2tex (ast),
					'simple': sym.ast2simple (ast),
					'py'    : sym.ast2py (ast),
				}

			except Exception:
				response = {'err': ''.join (traceback.format_exception (*sys.exc_info ())).replace ('  ', '&emsp;').strip ().split ('\n')}

		response ['mode'] = request ['mode']
		response ['idx']  = request ['idx']
		response ['text'] = request ['text']

		self.send_response (200)
		self.send_header ("Content-type", "application/json")
		self.end_headers ()
		self.wfile.write (json.dumps (response).encode ('utf8'))

# class ThreadingHTTPServer (ThreadingMixIn, HTTPServer):
# 	pass

#...............................................................................................
_month_name = (None, 'Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun', 'Jul', 'Aug', 'Sep', 'Oct', 'Nov', 'Dec')

if __name__ == '__main__':
	try:
		if 'SYMPAD_RUNNED_AS_WATCHED' not in os.environ:
			args      = [sys.executable] + sys.argv
			first_run = '1'

			while 1:
				ret = subprocess.run (args, env = {**os.environ, 'SYMPAD_RUNNED_AS_WATCHED': '1', 'SYMPAD_FIRST_RUN': first_run})

				if ret.returncode != 0:
					sys.exit (0)

				first_run = ''

		opts, argv = getopt.getopt (sys.argv [1:], '', ['debug', 'nobrowser'])

		if ('--debug', '') in opts:
			os.environ ['SYMPAD_DEBUG'] = '1'

		if not argv:
			host, port = _DEFAULT_ADDRESS
		else:
			host, port = (re.split (r'(?<=\]):' if argv [0].startswith ('[') else ':', argv [0]) + [_DEFAULT_ADDRESS [1]]) [:2]
			host, port = host.strip ('[]'), int (port)

		watch   = ('sympad.py',) if _RUNNING_AS_SINGLE_SCRIPT else ('lalr1.py', 'sparser.py', 'sym.py', 'server.py')
		tstamps = [os.stat (fnm).st_mtime for fnm in watch]
		httpd   = HTTPServer ((host, port), Handler) # ThreadingHTTPServer ((host, port), Handler)
		thread  = threading.Thread (target = httpd.serve_forever, daemon = True)

		thread.start ()

		def log_message (msg):
			y, m, d, hh, mm, ss, _, _, _ = time.localtime (time.time ())

			sys.stderr.write (f'{httpd.server_address [0]} - - ' \
					f'[{"%02d/%3s/%04d %02d:%02d:%02d" % (d, _month_name [m], y, hh, mm, ss)}] {msg}\n')

		log_message (f'Serving on {httpd.server_address [0]}:{httpd.server_address [1]}')

		if os.environ.get ('SYMPAD_FIRST_RUN') and ('--nobrowser', '') not in opts:
			webbrowser.open (f'http://{httpd.server_address [0] if httpd.server_address [0] != "0.0.0.0" else "127.0.0.1"}:{httpd.server_address [1]}/')

		while 1:
			time.sleep (0.5)

			if [os.stat (fnm).st_mtime for fnm in watch] != tstamps:
				log_message ('Files changed, restarting...')
				sys.exit (0)

	except OSError as e:
		if e.errno != 98:
			raise

		print (f'Port {port} seems to be in use, try specifying different address and/or port as a command line parameter, e.g. localhost:8001')

	except KeyboardInterrupt:
		sys.exit (0)

	sys.exit (-1)
