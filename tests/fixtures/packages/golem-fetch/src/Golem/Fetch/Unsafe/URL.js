import url from "node:url";

/** URLSearchParams */
export const _search_empty = new url.URLSearchParams();

export const _search_make = o => new url.URLSearchParams(o);

export const _search_traceShow = s => {
	console.log(s);
	return s;
};

export const _search_toString = s => s.toString();

export const _search_append = key => value => search => {
	const clone = _search_make(search);
	clone.append(key, value);
	return clone;
};

export const _search_delete = key => search => {
	const clone = _search_make(search);
	clone.delete(key);
	return clone;
};

export const _search_entries = tuple => search => {
	let xs = [];
	for (const [a, b] of search.entries()) {
		xs.push(tuple(a)(b));
	}
	return xs;
};

export const _search_get = just => nothing => key => search => {
	const v = search.get(key);
	if (v === null) {
		return nothing;
	}
	else {
		return just(v);
	}
};

export const _search_getAll = key => search => search.getAll(key);

export const _search_has = key => search => search.has(key);

export const _search_keys = search => {
	let xs = [];
	for (const k of search.keys()) {
		xs.push(k);
	}
	return xs;
};

export const _search_set = key => value => search => {
	let clone = _search_make(search);
	clone.set(key, value);
	return clone;
};

export const _search_size = search => search.size;

export const _search_values = search => search.values();
/** end URLSearchParams */

/** URL */
export const _url_make = input => new url.URL(input);

export const _url_toString = input => input.toString();

export const _url_traceShow = u => {
	console.log(u);
	return u;
};

export const _url_hash = u => u.hash;
export const _url_setHash = hash => u => {
	const clone = _url_make(u);
	clone.hash = hash;
	return clone;
};

export const _url_host = u => u.host;
export const _url_setHost = host => u => {
	const clone = _url_make(u);
	clone.host = host;
	return clone;
};

export const _url_hostname = u => u.hostname;
export const _url_setHostname = hostname => u => {
	const clone = _url_make(u);
	clone.hostname = hostname;
	return clone;
};

export const _url_href = u => u.href;
export const _url_setHref = href => u => {
	const clone = _url_make(u);
	clone.href = href;
	return clone;
};

export const _url_origin = u => u.origin;

export const _url_password = u => u.password;
export const _url_setPassword = password => u => {
	const clone = _url_make(u);
	clone.password = password;
	return clone;
};

export const _url_pathname = u => u.pathname;
export const _url_setPathname = pathname => u => {
	const clone = _url_make(u);
	clone.pathname = pathname;
	return clone;
};

export const _url_port = u => u.port;
export const _url_setPort = port => u => {
	const clone = _url_make(u);
	clone.port = port;
	return clone;
};

export const _url_protocol = u => u.protocol;
export const _url_setProtocol = protocol => u => {
	const clone = _url_make(u);
	clone.protocol = protocol;
	return clone;
};

export const _url_search = u => u.search;
export const _url_setSearch = search => u => {
	const clone = _url_make(u);
	clone.search = search;
	return clone;
};

export const _url_searchParams = u => u.searchParams;

export const _url_username = u => u.username;
export const _url_setUsername = username => u => {
	const clone = _url_make(u);
	clone.username = username;
	return clone;
};
/** end URL */
