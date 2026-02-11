/** headers */
export const _headers_empty = new Headers();
export const _headers_make = a => new Headers(a);

export const _headers_show = h => {
	let p = "";
	for (const [key, value] of h.entries()) {
		p += `${key}: ${value}, `;
	}

	return `Headers { ${p}}`;
};

export const _headers_append = key => value => h => {
	const clone = _headers_make(h);
	clone.append(key, value);
	return clone;
};

export const _headers_delete = key => h => {
	const clone = _headers_make(h);
	clone.delete(key);
	return clone;
};

export const _headers_entries = tuple => h => {
	let xs = [];
	for (const [key, value] of h.entries()) {
		xs.push(tuple(key)(value));
	}
	return xs;
};

export const _headers_get = just => nothing => key => h => {
	const v = h.get(key);
	if (v === null) {
		return nothing;
	}
	else {
		return just(v);
	}
};

export const _headers_has = key => h => h.has(key);

export const _headers_keys = h => {
	let xs = [];
	for (const key of h.keys()) {
		xs.push(key);
	}
	return xs;
};

export const _headers_set = key => value => h => {
	const clone = _headers_make(h);
	clone.set(key, value);
	return clone;
};

export const _headers_values = h => {
	let xs = [];
	for (const value of h.values()) {
		xs.push(value);
	}
	return xs;
};
/** end headers */

/** response */
export const _response_body = rsp => rsp.body;
export const _response_bodyUsed = rsp => rsp.bodyUsed;
export const _response_headers = rsp => rsp.headers
export const _response_ok = rsp => rsp.ok;
export const _response_redirected = rsp => rsp.redirected;
export const _response_status = rsp => rsp.status;
export const _response_statusText = rsp => rsp.statusText;
export const _response_type = rsp => rsp.type;
export const _response_json = rsp => (onFail, onOk) => {
	rsp.json().then(onOk).catch(onFail);

	return (_, __, onCancelOk) => {
		onCancelOk();
	};
};
export const _response_text = rsp => (onFail, onOk) => {
	rsp.text().then(onOk).catch(onFail);

	return (_, __, onCancelOk) => {
		onCancelOk();
	};
};
/** end response */

/** fetch */
export const _fetch_api = url => (onFail, onOk) => {
	fetch(url).then(onOk).catch(onFail);

	return (_cancelError, _onCancelFail, onCancelOk) => {
		onCancelOk();
	};
};

export const _fetch_api2 = url => opt => (onFail, onOk) => {
	fetch(url, opt).then(onOk).catch(onFail);

	return (_cancelError, _onCancelFail, onCancelOk) => {
		onCancelOk();
	};
};
/** end fetch */

/** misc */
export const _unwrap_maybe = fromMaybe => input => {
	let o = {};
	for (const key in input) {
		const v = input[key];
		o[key] = fromMaybe(undefined)(v);
	}

	console.log(o);
	return o;
};
/** end misc */
