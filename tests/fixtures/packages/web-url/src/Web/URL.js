"use strict";

export function urlImpl (just) {
  return function (nothing) {
    return function (base) {
      try {
        return just(new URL(base))
      } catch (TypeError) {
        return nothing
      }
    }
  }
}

export function url2Impl (just) {
  return function (nothing) {
    return function (rel) {
      return function (base) {
        try {
          return just(new URL(rel, base))
        } catch (TypeError) {
          return nothing
        }
      }
    }
  }
}

export function toString (url) {
  return url.toString()
}

export function hash (url) {
  return url.hash
}

export function host (url) {
  return url.host
}

export function hostname (url) {
  return url.hostname
}

export function href (url) {
  return url.href
}

export function origin (url) {
  return url.origin
}

export function password (url) {
  return url.password
}

export function pathname (url) {
  return url.pathname
}

export function port (url) {
  return url.port
}

export function protocol (url) {
  return url.protocol
}

export function search (url) {
  return url.search
}

export function searchParams (url) {
  return url.searchParams
}

export function username (url) {
  return url.username
}

export function setHash (v) {
  return function (url) {
    var u = new URL(url)
    u.hash = v
    return u
  }
}

export function setHost (v) {
  return function (url) {
    var u = new URL(url)
    u.host = v
    return u
  }
}

export function setHostname (v) {
  return function (url) {
    var u = new URL(url)
    u.hostname = v
    return u
  }
}

export function setHref (v) {
  return function (url) {
    var u = new URL(url)
    u.href = v
    return u
  }
}

export function setPassword (v) {
  return function (url) {
    var u = new URL(url)
    u.password = v
    return u
  }
}

export function setPathname (v) {
  return function (url) {
    var u = new URL(url)
    u.pathname = v
    return u
  }
}

export function setPort (v) {
  return function (url) {
    var u = new URL(url)
    u.port = v
    return u
  }
}

export function setProtocol (v) {
  return function (url) {
    var u = new URL(url)
    u.protocol = v
    return u
  }
}

export function setSearch (v) {
  return function (url) {
    var u = new URL(url)
    u.search = v
    return u
  }
}

export function setUsername (v) {
  return function (url) {
    var u = new URL(url)
    u.username = v
    return u
  }
}
