// TODO: Change how left/right arrows interact with autocomplete.
// TODO: Stupid scrollbars...
// TODO: Change input to text field for longer expression support?
// TODO: Arrow keys in Edge?
// TODO: clear() function to delete old log items?

URL              = '/';
WaitIcon         = '/wait.webp'; // 'https://i.gifer.com/origin/3f/3face8da2a6c3dcd27cb4a1aaa32c926_w200.webp';

JQInput          = null;
MJQueue          = null;
MarginTop        = Infinity;
PreventFocusOut  = true;

LogIdx           = 0;
UniqueID         = 1;

LastValidation   = null;
Validations      = [undefined];
Evaluations      = [undefined];
ErrorIdx         = null;
Autocomplete     = [];

LastClickTime    = 0;
NumClicks        = 0;

GreetingFadedOut = false;
ExceptionDone    = false;
SymPyDevVersion  = '1.4'

// replaced in env.js
History          = [];
HistIdx          = 0;
Version          = 'None'
SymPyVersion     = 'None'
DisplayStyle     = 1

//...............................................................................................
function copyInputStyle () {
	let left = $('#LogEntry1').position ().left;

	JQInput.css ({left: left});
	JQInput.width (window.innerWidth - left - 32);
	$('#InputCoverLeft').width (left);
	$('#InputCoverRight').css ({left: window.innerWidth - 30});

	let style   = getComputedStyle (document.getElementById ('Input'));
	let overlay = document.getElementById ('InputOverlay');

  for (let prop of style) {
    overlay.style [prop] = style [prop];
	}

	overlay.style ['z-index']        = 4;
	overlay.style ['pointer-events'] = 'none';
}

function scrollToEnd () {
	window.scrollTo (0, document.body.scrollHeight);
}

function resize () {
	copyInputStyle ();
	scrollToEnd ();
}

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

function reprioritizeMJQueue () {
	let p = MJQueue.queue.pop ();

	if (p !== undefined) {
		MJQueue.queue.splice (0, 0, p);
	}
}

function escapeHTML (text) {
	const entityMap = {
		'&': '&amp;',
		'<': '&lt;',
		'>': '&gt;',
		'"': '&quot;',
		"'": '&#39;',
		'/': '&#x2F;',
		'`': '&#x60;',
		'=': '&#x3D;'
	};

	return text.replace (/[&<>"'`=\/]/g, function (s) {
		return entityMap [s];
	});
}

function escapeHTMLtex (text) {
	return text.replace (/\\text{(['"]).*?\1}/g, escapeHTML);
}

//...............................................................................................
function logResize () {
	let margin = Math.max (BodyMarginTop, Math.floor (window.innerHeight - $('body').height () - BodyMarginBottom + 3)); // +3 is fudge factor

	if (margin < MarginTop) {
		MarginTop = margin;
		$('body').css ({'margin-top': margin});
	}
}

function addLogEntry () {
	LogIdx += 1;

	$('#Log').append (`
			<div class="LogEntry"><div class="LogMargin">${LogIdx}.</div><div class="LogBody" id="LogEntry${LogIdx}"><div class="LogInput" id="LogInput${LogIdx}">
				<img class="LogWait" id="LogInputWait${LogIdx}" src="${WaitIcon}" width="16" style="visibility: hidden">
			</div></div></div>`)

	Validations.push (undefined);
	Evaluations.push (undefined);
}

function updateNumClicks () {
	let t = performance.now ();

	if ((t - LastClickTime) > 500) {
		NumClicks = 1;
	} else {
		NumClicks += 1;
	}

	LastClickTime = t;
}

function flashElement (e) {
	e.style.color      = 'white';
	e.style.background = 'black';

	setTimeout (function () {
		e.style.color      = 'black';
		e.style.background = 'transparent';
	}, 100);
}

function writeToClipboard (text) {
	PreventFocusOut = false;

	$('#Clipboard').val (text);
	$('#Clipboard').focus ();
	$('#Clipboard').select ();
	document.execCommand ('copy');

	PreventFocusOut = true;

	if (JQInput !== null) {
		JQInput.focus ();
	}
}

function cE2C (e) {
	writeToClipboard (e.textContent);
	flashElement (e);
}

function copyLogToClipboard (e, val_or_eval, idx, subidx = 0, mathidx = 0) {
	let resp = val_or_eval ? Evaluations [idx].data [subidx].math [mathidx] : Validations [idx];

	updateNumClicks ();
	writeToClipboard (NumClicks == 1 ? resp.nat : NumClicks == 2 ? resp.py : resp.tex);
	flashElement (e);
}

function copyVarToClipboard (e, full = true) {
	updateNumClicks ();

	e        = e.parentElement;
	let text = Variables.vars.get (e.name);
	text     = NumClicks == 1 ? text.nat : NumClicks == 2 ? text.py : text.tex;

	if (!full && (NumClicks == 2) && text [1].startsWith ('Lambda(')) { // special case process py Lambda body
		if (text [1] [7] === '(') {
			text = [text [0], text [1].slice (text [1].indexOf (')') + 2, -1).trim ()];
		} else {
			text = [text [0], text [1].slice (text [1].indexOf (',') + 1, -1).trim ()];
		}
	}

	writeToClipboard (full ? text.join (' = ') : text [1]);
	flashElement (full ? e : e.childNodes [2]);
}

function updateOverlayPosition () {
	let left       = -JQInput.scrollLeft ();
	let goodwidth  = $('#OverlayGood').width ();
	let errorwidth = $('#OverlayError').width ();

	$('#OverlayGood').css ({left: left})
	$('#OverlayError').css ({top: 0, left: left + goodwidth});
	$('#OverlayAutocomplete').css ({top: 0, left: left + goodwidth + errorwidth});
}

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
function ajaxValidate (resp) {
	if (Validations [resp.idx] !== undefined && Validations [resp.idx].subidx >= resp.subidx) {
		return; // ignore out of order responses (which should never happen with single threaded server)
	}

	LastValidation = resp;

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

		$(eLogInput).append (`<span class="CopySpan" onclick="copyLogToClipboard (this, 0, ${resp.idx})" style="visibility: hidden">${escapeHTMLtex (math)}</span>`);

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
}

function ajaxEvaluate (resp) {
	Variables.update (resp.vars);

	Evaluations [resp.idx] = resp;
	let eLogEval           = document.getElementById ('LogEval' + resp.idx);

	eLogEval.removeChild (document.getElementById ('LogEvalWait' + resp.idx));

	for (let subidx in resp.data) {
		subresp = resp.data [subidx];

		if (subresp.msg !== undefined && subresp.msg.length) { // message present?
			for (let msg of subresp.msg) {
				$(eLogEval).append (`<div class="LogMsg">${escapeHTML (msg.replace (/  /g, '&emsp;'))}</div>`);
			}

			logResize ();
			scrollToEnd ();
		}

		if (subresp.math !== undefined && subresp.math.length) { // math results present?
			for (let mathidx in subresp.math) {
				$(eLogEval).append (`<div class="LogEval"></div>`);
				let eLogEvalDiv = eLogEval.lastElementChild;

				$(eLogEvalDiv).append (`<span class="CopySpan" style="visibility: hidden" onclick="copyLogToClipboard (this, 1, ${resp.idx}, ${subidx}, ${mathidx})">$${escapeHTMLtex (subresp.math [mathidx].tex)}$</span>`);
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
					$(eLogErrorHidden).append (`<div class="LogError">${escapeHTML (subresp.err [i].replace (/  /g, '&emsp;'))}</div>`);
				}
			}

			$(eLogEval).append (`<div class="LogError">${escapeHTML (subresp.err [subresp.err.length - 1])}</div>`);
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
		success: ajaxValidate,
		data: {
			mode: 'validate',
			idx: LogIdx,
			subidx: UniqueID ++,
			text: text,
		},
	});
}

function inputted (text) {
	$.ajax ({
		url: URL,
		type: 'POST',
		cache: false,
		dataType: 'json',
		success: ajaxEvaluate,
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

		} else if (LastValidation !== null && LastValidation.error) { // last validation had error, display
			let eLogInput = document.getElementById (`LogInput${LastValidation.idx}`);

			$('#ValidationError').remove ();
			$(eLogInput).append (`<span id="ValidationError">&lt;-- ${escapeHTML (LastValidation.error)}</span>`)
		}

	} else if (e.which == 32) {
		if (!JQInput.val ()) {
			return false;
		}
	}

	return true;
}

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

			text         = text + Autocomplete [0];
			Autocomplete = Autocomplete.slice (1);

			JQInput.val (text);
			inputting (text);
		}
	}

	setTimeout (updateOverlayPosition, 0);

	return true;
}

//...............................................................................................
class _Variables {
	constructor () {
		this.eVarDiv       = document.getElementById ('VarDiv');
		this.eVarTab       = document.getElementById ('VarTab');
		this.eVarContent   = document.getElementById ('VarContent');
		this.eVarTable     = document.getElementById ('VarTable');
		this.queued_update = null;
		this.display       = true;
		this.vars          = new Map ();
	}

	_update (vars) {
		function spliteq (text) {
			let p = text.split (' = ');

			return [p [0], p.slice (1).join (' = ')];
		}

		vars = new Map (vars.map (function (e) {
			let nat = spliteq (e.nat);

			return [nat [0], {tex: spliteq (e.tex), nat: nat, py: spliteq (e.py)}];
		}));

		let same = new Set ();

		for (let r of Array.from (this.eVarTable.childNodes)) {
			let v = vars.get (r.name);

			if (v === undefined || r.val !== v.tex.join (' = ')) {
				this.eVarTable.removeChild (r);
			} else {
				same.add (r.name);
			}
		}

		let added = false;

		for (let [n, v] of vars) {
			if (same.has (n)) {
				continue;
			}

			let inserted = false;
			let isfunc   = n.includes ('(');
			let e        = $(`<tr><td onclick="copyVarToClipboard (this)">$${escapeHTMLtex (v.tex [0])}$</td><td class="VarTCell" onclick="copyVarToClipboard (this)">$=$</td><td class="VarTCell" onclick="copyVarToClipboard (this, false)">$${escapeHTMLtex (v.tex [1])}$</td></tr>`);
			e [0].name   = n;
			e [0].val    = v.tex.join (' = ');
			added        = true;

			for (let r of this.eVarTable.childNodes) {
				let isfuncr = r.name.includes ('(');

				if ((isfunc && !isfuncr) || ((n < r.name) && (isfunc === isfuncr))) {
					e.insertBefore (r);
					inserted = true;

					break;
				}
			}

			if (!inserted) {
				e.appendTo (this.eVarTable);
			}
		}

		this.vars = vars;

		if (added) {
			MJQueue.Push (['Typeset', MathJax.Hub, this.eVarTable]);
			reprioritizeMJQueue ();
		}
	}

	update (vars) {
		if (this.display) {
			this._update (vars);
		} else {
			this.queued_update = vars;
		}

		this.eVarDiv.style.display = vars.length ? 'block' : 'none';
	}

	toggle () {
		this.eVarContent.style.minWidth = `${this.eVarTab.clientWidth + 2}px`;

		if (!this.display && this.queued_update !== null) {
			this._update (this.queued_update);
			this.queued_update = null;
		}

		this.display                   = !this.display;
		this.eVarContent.style.display = this.display ? 'block' : 'none';
	}
}

//...............................................................................................
$(function () {
	if (window.location.pathname != '/') {
		return;
	}

	window.JQInput   = $('#Input');
	window.Variables = new _Variables ();

	let margin       = $('body').css ('margin-top');
	BodyMarginTop    = Number (margin.slice (0, margin.length - 2));
	margin           = $('body').css ('margin-bottom');
	BodyMarginBottom = Number (margin.slice (0, margin.length - 2));

	$('#Clipboard').prop ('readonly', true);
	$('#InputCover') [0].height = $('#InputCover').height ();

	JQInput.keypress (inputKeypress);
	JQInput.keydown (inputKeydown);

	addLogEntry ();
	logResize ();
	resize ();
	monitorStuff ();

	function first_vars_update (resp) {
		if (MJQueue === null) { // wait for MathJax ready
			setTimeout (function () { first_vars_update (resp); }, 50);
		} else {
			Variables.update (resp.vars);
		}
	}

	$.ajax ({
		url: URL,
		type: 'POST',
		cache: false,
		dataType: 'json',
		success: first_vars_update,
		data: {mode: 'vars'},
	});
});
