var URL             = '/';
var MJQueue         = null;
var PreventFocusOut = true;

var History         = [];
var HistIdx         = 0;
var LogIdx          = 0;
var ErrorIdx        = null;
var UniqueId        = 0;
var Autocomplete    = [];
var MarginTop       = Infinity;

//-----------------------------------------------------------------------------------------------

//...............................................................................................
function generateBG () {
	function writeRandomData (data, x0, y0, width, height) {
		let p, d;

		for (let y = y0; y < height; y ++) {
			p = (width * y + x0) * 4;

			for (let x = x0; x < width; x ++) {
				d            = 244 + Math.floor (Math.random () * 12);
				data [p]     = data [p + 1] = d; // data [p + 2] = d
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

	canv        = $('#InputBG') [0];
	ctx         = canv.getContext ('2d');
	canv.width  = window.innerWidth;

	ctx.putImageData (imgd, 0, 0);
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
	// overlay.style.width               = 'auto';
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
	let body   = $('body');
	let margin = Math.max (BodyMarginTop, Math.floor (window.innerHeight - body.height () - BodyMarginBottom + 2)); // 2 is fudge factor

	if (margin < MarginTop) {
		window.MarginTop = margin
		body.css ({'margin-top': margin});
	}
}

//...............................................................................................
function readyMathJax () {
	window.MJQueue = MathJax.Hub.queue;

	var TEX        = MathJax.InputJax.TeX;
	var PREFILTER  = TEX.prefilterMath;

	TEX.Augment ({
		prefilterMath: (tex, displaymode, script) => {
			// tex = '\\displaystyle{' + tex.replace ('\\right|', '\\ \\right|') + '}'
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

	$('#Log').append ('<li class="LogEntry" id="LogEntry' + LogIdx + '"><div id="LogInput' + LogIdx + '" class="LogLine">' +
			'<img id="LogInputWait' + LogIdx + '" class="LogInputWait" src="https://i.gifer.com/origin/3f/3face8da2a6c3dcd27cb4a1aaa32c926_w200.webp" width="16" style="visibility: hidden">' +
			'</div></li>');
}

//...............................................................................................
function parseTeX (text) {
	return text.replace (/(\\left|\\right)(\(|\)|\[|\])/g, '$2').replace (/\\operatorname{(sech|csch)}/g, '\\$1')
			.replace (/\\operatorname{(\?|\w+)}/g, '$1');
}

//...............................................................................................
function copyToClipboard (elem) {
	window.PreventFocusOut = false;

	$('#Clipboard').val (parseTeX ($('#' + elem.id + ' > script').text ()));
	$('#Clipboard').focus ();
	$('#Clipboard').select ();

	document.execCommand ('copy');

	window.PreventFocusOut = true;

	JQInput.focus ();

	elem.style.color      = 'transparent';
	elem.style.background = 'black';

	setTimeout (() => {
		elem.style.color      = 'black';
		elem.style.background = 'transparent';
	}, 100);
}

//-----------------------------------------------------------------------------------------------

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
		if (resp.tex !== null) {
			let eLogInput = document.getElementById ('LogInput' + resp.idx);
			let queue     = [];

			[queue, MJQueue.queue] = [MJQueue.queue, queue];

			MJQueue.queue = queue.filter (function (obj, idx, arr) { // remove previous pending updates to same element
				return obj.data [0].parentElement !== eLogInput;
			})

			let idMath        = 'LogInputMath' + (++ UniqueId);
			let eLogInputWait = document.getElementById ('LogInputWait' + resp.idx);

			eLogInputWait.style.visibility = '';

			$(eLogInput).append ('<span id="' + idMath + '" onclick="copyToClipboard (this)" style="visibility: hidden">$' + resp.tex + '$</span>');

			let eMath = document.getElementById (idMath);

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
		let eLogEval = document.getElementById ('LogEval' + resp.idx);

		if (resp.err !== undefined) {
			eLogEval.removeChild (document.getElementById ('LogEvalWait' + resp.idx));

			if (resp.err.length > 1) {
				let idLogErrorHidden = 'LogErrorHidden' + resp.idx;

				$(eLogEval).append ('<div id="' + idLogErrorHidden + '" style="display: none"></div>');

				var eLogErrorHidden = document.getElementById (idLogErrorHidden);

				for (let i = 0; i < resp.err.length - 1; i ++) {
					$(eLogErrorHidden).append ('<div class="LogError">' + resp.err [i] + '</div>');
				}
			}

			let idLogErrorTriangle = 'LogErrorTriangle' + resp.idx;

			$(eLogEval).append ('<div class="LogError">' + resp.err [resp.err.length - 1] + '<span id="LogErrorTriangle' + resp.idx + '" class="LogErrorTriange">\u25b6</span></div>');

			var eLogErrorTriangle = document.getElementById (idLogErrorTriangle);

			$(eLogEval).click (function () { // '\u25b2\u25ba\u25b3\u25b7'
				if (eLogErrorHidden.style.display === 'none') {
					eLogErrorHidden.style.display = 'block';
					eLogErrorTriangle.innerText   = '\u25b2'; // '\u25b9' // '\u25b4' // '\u25b3' //
				} else {
					eLogErrorHidden.style.display = 'none';
					eLogErrorTriangle.innerText   = '\u25b6'; // '\u25b5' // '\u25b8' // '\u25b7' //
				}

				logResize ();

				// eLogErrorHidden.style.display = eLogErrorHidden.style.display === 'none' ? 'block' : 'none';
				// logResize ();
			});

			logResize ();
			scrollToEnd ();

		} else { // no error
			let idEvalMath   = 'LogEvalMath' + resp.idx;

			$(eLogEval).append ('<span id="' + idEvalMath + '" style="visibility: hidden" onclick="copyToClipboard (this)">$' + resp.tex + '$</span>');

			let eLogEvalMath = document.getElementById (idEvalMath);

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
		data: {mode: 'validate', idx: LogIdx, text: text, csrfmiddlewaretoken: window.CSRF_TOKEN},
		cache: false,
		dataType: 'json',
		success: ajaxResponse
	});
}

//...............................................................................................
function inputted (text) {
	$.ajax ({
		url: URL,
		type: 'POST',
		data: {mode: 'evaluate', idx: LogIdx, text: text, csrfmiddlewaretoken: window.CSRF_TOKEN},
		cache: false,
		dataType: 'json',
		success: ajaxResponse
	});

	$('#LogEntry' + LogIdx).append ('<div id="LogEval' + LogIdx + '">' +
			'<img id="LogEvalWait' + LogIdx + '" class="LogLine" src="https://i.gifer.com/origin/3f/3face8da2a6c3dcd27cb4a1aaa32c926_w200.webp" width="16">' +
			'</div>');

	History.push (text);

	HistIdx = History.length;

	addLogEntry ();
	logResize ();
	scrollToEnd ();
}

//-----------------------------------------------------------------------------------------------

//...............................................................................................
function inputKeypress (e) {
	if (e.which == 13) {
		s = JQInput.val ().trim ();

		if (s && ErrorIdx === null) {
			s = s + Autocomplete.join ('');

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

		} else {
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
			updateOverlay (text, ErrorIdx, Autocomplete);
		}
	}
}

//...............................................................................................
function inputFocusout (e) {
	if (PreventFocusOut) {
		e.preventDefault ();
		$(this).focus ();
	}
}

//...............................................................................................
$(function () {
	window.JQInput = $('#Input');

	let margin              = $('body').css ('margin-top');
	window.BodyMarginTop    = Number (margin.slice (0, margin.length - 2));
	margin                  = $('body').css ('margin-bottom');
	window.BodyMarginBottom = Number (margin.slice (0, margin.length - 2));

	addLogEntry ();

	JQInput.keypress (inputKeypress);
	JQInput.keydown (inputKeydown);
	JQInput.focusout (inputFocusout);

	$('#Clipboard').prop ('readonly', true);
	$('#InputBG') [0].height = $('#InputBG').height ();

	logResize ();
	resize ();
});


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
