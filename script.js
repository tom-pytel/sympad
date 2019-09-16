// TODO: Change how left/right arrows interact with autocomplete.
// TODO: Stupid scrollbars...
// TODO: Change input to text field for longer expression support?
// TODO: Arrow keys in Edge?
// TODO: clear() function to delete old log items?

URL              = '/';
WaitIcon         = 'https://i.gifer.com/origin/3f/3face8da2a6c3dcd27cb4a1aaa32c926_w200.webp';

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
ExceptionDone    = false;

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
		for (let name of ['#InputBG', '#InputBGLeft', '#InputBGRight']) {
			canv        = $(name) [0];
			ctx         = canv.getContext ('2d');
			canv.width  = window.innerWidth;

			ctx.putImageData (imgd, 0, 0);
		}
	}
}

//...............................................................................................
function copyInputStyle () {
	let left = $('#LogEntry1').position ().left;

	JQInput.css ({left: left});
	JQInput.width (window.innerWidth - left - 32);
	$('#InputBGLeft').width (left);
	$('#InputBGRight').css ({left: window.innerWidth - 30});

	let style   = getComputedStyle (document.getElementById ('Input'));
	let overlay = document.getElementById ('InputOverlay');

  for (let prop of style) {
    overlay.style [prop] = style [prop];
	}

	overlay.style ['z-index']        = 4;
	overlay.style ['pointer-events'] = 'none';
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
		MarginTop = margin;
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

	updateOverlayPosition ();
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
				<img class="LogWait" id="LogInputWait${LogIdx}" src="${WaitIcon}" width="16" style="visibility: hidden">
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
function copyToClipboard (e, val_or_eval, idx, subidx = 0, mathidx = 0) {
	let t = performance.now ();

	if ((t - LastClickTime) > 500) {
		NumClicks = 1;
	} else{
		NumClicks += 1;
	}

	LastClickTime = t;
	let resp      = val_or_eval ? Evaluations [idx].data [subidx].math [mathidx] : Validations [idx];

	writeToClipboard (NumClicks == 1 ? resp.nat : NumClicks == 2 ? resp.py : resp.tex);

	e.style.color      = 'transparent';
	e.style.background = 'black';

	setTimeout (function () {
		e.style.color      = 'black';
		e.style.background = 'transparent';
	}, 100);
}

//...............................................................................................
function updateOverlayPosition () {
	let left       = -JQInput.scrollLeft ();
	let goodwidth  = $('#OverlayGood').width ();
	let errorwidth = $('#OverlayError').width ();

	$('#OverlayGood').css ({left: left})
	$('#OverlayError').css ({top: 0, left: left + goodwidth});
	$('#OverlayAutocomplete').css ({top: 0, left: left + goodwidth + errorwidth});
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

	updateOverlayPosition ();
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
			});

			let eLogInputWait              = document.getElementById ('LogInputWait' + resp.idx);
			let math                       = resp.tex ? `$${resp.tex}$` : '';
			eLogInputWait.style.visibility = '';

			$(eLogInput).append (`<span onclick="copyToClipboard (this, 0, ${resp.idx})" style="visibility: hidden">${math}</span>`);
			let eMath = eLogInput.lastElementChild;

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
		let eLogEval           = document.getElementById ('LogEval' + resp.idx);

		eLogEval.removeChild (document.getElementById ('LogEvalWait' + resp.idx));

		for (let subidx in resp.data) {
			subresp = resp.data [subidx];

			if (subresp.msg !== undefined && subresp.msg.length) { // message present?
				for (let msg of subresp.msg) {
					$(eLogEval).append (`<div class="LogMsg">${msg.replace (/  /g, '&emsp;')}</div>`);
				}

				logResize ();
				scrollToEnd ();
			}

			if (subresp.math !== undefined && subresp.math.length) { // math results present?
				for (let mathidx in subresp.math) {
					$(eLogEval).append (`<div class="LogEval"></div>`);
					let eLogEvalDiv = eLogEval.lastElementChild;

					$(eLogEvalDiv).append (`<span style="visibility: hidden" onclick="copyToClipboard (this, 1, ${resp.idx}, ${subidx}, ${mathidx})">$${subresp.math [mathidx].tex}$</span>`);
					let eLogEvalMath = eLogEvalDiv.lastElementChild;

					$(eLogEvalDiv).append (`<img class="LogWait" src="${WaitIcon}" width="16">`);
					let eLogEvalWait = eLogEvalDiv.lastElementChild;

					MJQueue.Push (['Typeset', MathJax.Hub, eLogEvalMath, function () {
						eLogEvalDiv.removeChild (eLogEvalWait);

						eLogEvalMath.style.visibility = '';

						logResize ();
						scrollToEnd ();
					}]);

					reprioritizeMJQueue ();
				}
			}

			if (subresp.err !== undefined) { // error?
				let eErrorHiddenBox, eLogErrorHidden;

				if (subresp.err.length > 1) {
					$(eLogEval).append ('<div style="position: relative"></div>');
					eErrorHiddenBox = eLogEval.lastElementChild;

					$(eErrorHiddenBox).append (`<div style="display: none"></div>`);
					eLogErrorHidden = eErrorHiddenBox.lastElementChild;

					for (let i = 0; i < subresp.err.length - 1; i ++) {
						$(eLogErrorHidden).append (`<div class="LogError">${subresp.err [i].replace (/  /g, '&emsp;')}</div>`);
					}
				}

				$(eLogEval).append (`<div class="LogError">${subresp.err [subresp.err.length - 1]}</div>`);
				let eLogErrorBottom = eLogEval.lastElementChild;

				if (subresp.err.length > 1) {
					let ClickHereToOpen = null;

					if (!ExceptionDone) {
						$(eLogErrorBottom).append ('<i>&emsp;<-- click to open</i>');

						ClickHereToOpen = eLogErrorBottom.lastElementChild;
						ExceptionDone   = true;
					}

					$(eErrorHiddenBox).append (`<div class="LogErrorTriange">\u25b7</div>`);
					let eLogErrorTriangle = eErrorHiddenBox.lastElementChild;

					f = function () {
						if (eLogErrorHidden.style.display === 'none') {
							eLogErrorHidden.style.display = 'block';
							eLogErrorTriangle.innerText   = '\u25bd';
						} else {
							eLogErrorHidden.style.display = 'none';
							eLogErrorTriangle.innerText   = '\u25b7';
						}

						if (ClickHereToOpen) {
							ClickHereToOpen.parentNode.removeChild (ClickHereToOpen);
							ClickHereToOpen = null;
						}

						logResize ();
					};

					$(eLogErrorHidden).click (f);
					$(eLogErrorBottom).click (f);
					$(eLogErrorTriangle).click (f);
				}

				logResize ();
				scrollToEnd ();
			}

			if (subresp.img !== undefined) { // image present?
				$(eLogEval).append (`<div><img src='data:image/png;base64,${subresp.img}'></div>`);

				setTimeout (function () { // image seems to take some time to register size even though it is directly present
					logResize ();
					scrollToEnd ();
				}, 0);
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
				<img class="LogWait" id="LogEvalWait${LogIdx}" src="${WaitIcon}" width="16">
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

			// if ((Autocomplete [0] === ' \\right') || (Autocomplete [0] === '|')) {
			// 	text         = text + Autocomplete.slice (0, 2).join ('');
			// 	Autocomplete = Autocomplete.slice (2);

			// } else {
			// 	text         = text + Autocomplete [0];
			// 	Autocomplete = Autocomplete.slice (1);
			// }
			text         = text + Autocomplete [0];
			Autocomplete = Autocomplete.slice (1);

			JQInput.val (text);
			inputting (text);
			// updateOverlay (text, ErrorIdx, Autocomplete);
		}
	}

	setTimeout (updateOverlayPosition, 0);

	return true;
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
