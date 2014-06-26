 
            /*!
         * Sizzle CSS Selector Engine
         * Copyright 2012 jQuery Foundation and other contributors
         * Released under the MIT license
         * http://sizzlejs.com/
         */ (function (window, undefined) {

          var i, cachedruns, Expr, getText, isXML, compile, hasDuplicate, outermostContext,

          // Local document vars
          setDocument, document, docElem, documentIsXML, rbuggyQSA, rbuggyMatches, matches, contains, sortOrder,

          // Instance-specific data
          expando = "sizzle" + -(new Date()),
            preferredDoc = window.document,
            support = {},
            dirruns = 0,
            done = 0,
            classCache = createCache(),
            tokenCache = createCache(),
            compilerCache = createCache(),

            // General-purpose constants
            strundefined = typeof undefined,
            MAX_NEGATIVE = 1 << 31,

            // Array methods
            arr = [],
            pop = arr.pop,
            push = arr.push,
            slice = arr.slice,
            // Use a stripped-down indexOf if we can't use a native one
            indexOf = arr.indexOf ||
          function (elem) {
            var i = 0,
              len = this.length;
            for (; i < len; i++) {
              if (this[i] === elem) {
                return i;
              }
            }
            return -1;
          },


          // Regular expressions
          // Whitespace characters http://www.w3.org/TR/css3-selectors/#whitespace
          whitespace = "[\\x20\\t\\r\\n\\f]",
          // http://www.w3.org/TR/css3-syntax/#characters
          characterEncoding = "(?:\\\\.|[\\w-]|[^\\x00-\\xa0])+",

          // Loosely modeled on CSS identifier characters
          // An unquoted value should be a CSS identifier http://www.w3.org/TR/css3-selectors/#attribute-selectors
          // Proper syntax: http://www.w3.org/TR/CSS21/syndata.html#value-def-identifier
          identifier = characterEncoding.replace("w", "w#"),

          // Acceptable operators http://www.w3.org/TR/selectors/#attribute-selectors
          operators = "([*^$|!~]?=)", attributes = "\\[" + whitespace + "*(" + characterEncoding + ")" + whitespace + "*(?:" + operators + whitespace + "*(?:(['\"])((?:\\\\.|[^\\\\])*?)\\3|(" + identifier + ")|)|)" + whitespace + "*\\]",

          // Prefer arguments quoted,
          //   then not containing pseudos/brackets,
          //   then attribute selectors/non-parenthetical expressions,
          //   then anything else
          // These preferences are here to reduce the number of selectors
          //   needing tokenize in the PSEUDO preFilter
          pseudos = ":(" + characterEncoding + ")(?:\\(((['\"])((?:\\\\.|[^\\\\])*?)\\3|((?:\\\\.|[^\\\\()[\\]]|" + attributes.replace(3, 8) + ")*)|.*)\\)|)",

          // Leading and non-escaped trailing whitespace, capturing some non-whitespace characters preceding the latter
          rtrim = new RegExp("^" + whitespace + "+|((?:^|[^\\\\])(?:\\\\.)*)" + whitespace + "+$", "g"),

          rcomma = new RegExp("^" + whitespace + "*," + whitespace + "*"), rcombinators = new RegExp("^" + whitespace + "*([\\x20\\t\\r\\n\\f>+~])" + whitespace + "*"), rpseudo = new RegExp(pseudos), ridentifier = new RegExp("^" + identifier + "$"),

          matchExpr = {
            "ID": new RegExp("^#(" + characterEncoding + ")"),
            "CLASS": new RegExp("^\\.(" + characterEncoding + ")"),
            "NAME": new RegExp("^\\[name=['\"]?(" + characterEncoding + ")['\"]?\\]"),
            "TAG": new RegExp("^(" + characterEncoding.replace("w", "w*") + ")"),
            "ATTR": new RegExp("^" + attributes),
            "PSEUDO": new RegExp("^" + pseudos),
            "CHILD": new RegExp("^:(only|first|last|nth|nth-last)-(child|of-type)(?:\\(" + whitespace + "*(even|odd|(([+-]|)(\\d*)n|)" + whitespace + "*(?:([+-]|)" + whitespace + "*(\\d+)|))" + whitespace + "*\\)|)", "i"),
            // For use in libraries implementing .is()
            // We use this for POS matching in `select`
            "needsContext": new RegExp("^" + whitespace + "*[>+~]|:(even|odd|eq|gt|lt|nth|first|last)(?:\\(" + whitespace + "*((?:-\\d)?\\d*)" + whitespace + "*\\)|)(?=[^-]|$)", "i")
          },

          rsibling = /[\x20\t\r\n\f]*[+~]/,

          rnative = /^[^{]+\{\s*\[native code/,

          // Easily-parseable/retrievable ID or TAG or CLASS selectors
          rquickExpr = /^(?:#([\w-]+)|(\w+)|\.([\w-]+))$/,

          rinputs = /^(?:input|select|textarea|button)$/i, rheader = /^h\d$/i,

          rescape = /'|\\/g, rattributeQuotes = /\=[\x20\t\r\n\f]*([^'"\]]*)[\x20\t\r\n\f]*\]/g,

          // CSS escapes http://www.w3.org/TR/CSS21/syndata.html#escaped-characters
          runescape = /\\([\da-fA-F]{1,6}[\x20\t\r\n\f]?|.)/g, funescape = function (_, escaped) {
            var high = "0x" + escaped - 0x10000;
            // NaN means non-codepoint
            return high !== high ? escaped :
            // BMP codepoint
            high < 0 ? String.fromCharCode(high + 0x10000) :
            // Supplemental Plane codepoint (surrogate pair)
            String.fromCharCode(high >> 10 | 0xD800, high & 0x3FF | 0xDC00);
          };

          // Use a stripped-down slice if we can't use a native one
          try {
            slice.call(preferredDoc.documentElement.childNodes, 0)[0].nodeType;
          } catch (e) {
            slice = function (i) {
              var elem, results = [];
              while ((elem = this[i++])) {
                results.push(elem);
              }
              return results;
            };
          }

          /**
           * For feature detection
           * @param {Function} fn The function to test for native support
           */
          function isNative(fn) {
            return rnative.test(fn + "");
          }

          /**
           * Create key-value caches of limited size
           * @returns {Function(string, Object)} Returns the Object data after storing it on itself with
           *	property name the (space-suffixed) string and (if the cache is larger than Expr.cacheLength)
           *	deleting the oldest entry
           */
          function createCache() {
            var cache, keys = [];

            return (cache = function (key, value) {
              // Use (key + " ") to avoid collision with native prototype properties (see Issue #157)
              if (keys.push(key += " ") > Expr.cacheLength) {
                // Only keep the most recent entries
                delete cache[keys.shift()];
              }
              return (cache[key] = value);
            });
          }

          /**
           * Mark a function for special use by Sizzle
           * @param {Function} fn The function to mark
           */
          function markFunction(fn) {
            fn[expando] = true;
            return fn;
          }

          /**
           * Support testing using an element
           * @param {Function} fn Passed the created div and expects a boolean result
           */
          function assert(fn) {
            var div = document.createElement("div");

            try {
              return fn(div);
            } catch (e) {
              return false;
            } finally {
              // release memory in IE
              div = null;
            }
          }

          function Sizzle(selector, context, results, seed) {
            var match, elem, m, nodeType,
            // QSA vars
            i, groups, old, nid, newContext, newSelector;

            if ((context ? context.ownerDocument || context : preferredDoc) !== document) {
              setDocument(context);
            }

            context = context || document;
            results = results || [];

            if (!selector || typeof selector !== "string") {
              return results;
            }

            if ((nodeType = context.nodeType) !== 1 && nodeType !== 9) {
              return [];
            }

            if (!documentIsXML && !seed) {

              // Shortcuts
              if ((match = rquickExpr.exec(selector))) {
                // Speed-up: Sizzle("#ID")
                if ((m = match[1])) {
                  if (nodeType === 9) {
                    elem = context.getElementById(m);
                    // Check parentNode to catch when Blackberry 4.6 returns
                    // nodes that are no longer in the document #6963
                    if (elem && elem.parentNode) {
                      // Handle the case where IE, Opera, and Webkit return items
                      // by name instead of ID
                      if (elem.id === m) {
                        results.push(elem);
                        return results;
                      }
                    } else {
                      return results;
                    }
                  } else {
                    // Context is not a document
                    if (context.ownerDocument && (elem = context.ownerDocument.getElementById(m)) && contains(context, elem) && elem.id === m) {
                      results.push(elem);
                      return results;
                    }
                  }

                  // Speed-up: Sizzle("TAG")
                } else if (match[2]) {
                  push.apply(results, slice.call(context.getElementsByTagName(selector), 0));
                  return results;

                  // Speed-up: Sizzle(".CLASS")
                } else if ((m = match[3]) && support.getByClassName && context.getElementsByClassName) {
                  push.apply(results, slice.call(context.getElementsByClassName(m), 0));
                  return results;
                }
              }

              // QSA path
              if (support.qsa && !rbuggyQSA.test(selector)) {
                old = true;
                nid = expando;
                newContext = context;
                newSelector = nodeType === 9 && selector;

                // qSA works strangely on Element-rooted queries
                // We can work around this by specifying an extra ID on the root
                // and working up from there (Thanks to Andrew Dupont for the technique)
                // IE 8 doesn't work on object elements
                if (nodeType === 1 && context.nodeName.toLowerCase() !== "object") {
                  groups = tokenize(selector);

                  if ((old = context.getAttribute("id"))) {
                    nid = old.replace(rescape, "\\$&");
                  } else {
                    context.setAttribute("id", nid);
                  }
                  nid = "[id='" + nid + "'] ";

                  i = groups.length;
                  while (i--) {
                    groups[i] = nid + toSelector(groups[i]);
                  }
                  newContext = rsibling.test(selector) && context.parentNode || context;
                  newSelector = groups.join(",");
                }

                if (newSelector) {
                  try {
                    push.apply(results, slice.call(newContext.querySelectorAll(
                    newSelector), 0));
                    return results;
                  } catch (qsaError) {} finally {
                    if (!old) {
                      context.removeAttribute("id");
                    }
                  }
                }
              }
            }

            // All others
            return select(selector.replace(rtrim, "$1"), context, results, seed);
          }

          /**
           * Detect xml
           * @param {Element|Object} elem An element or a document
           */
          isXML = Sizzle.isXML = function (elem) {
            // documentElement is verified for cases where it doesn't yet exist
            // (such as loading iframes in IE - #4833)
            var documentElement = elem && (elem.ownerDocument || elem).documentElement;
            return documentElement ? documentElement.nodeName !== "HTML" : false;
          };

          /**
           * Sets document-related variables once based on the current document
           * @param {Element|Object} [doc] An element or document object to use to set the document
           * @returns {Object} Returns the current document
           */
          setDocument = Sizzle.setDocument = function (node) {
            var doc = node ? node.ownerDocument || node : preferredDoc;

            // If no document and documentElement is available, return
            if (doc === document || doc.nodeType !== 9 || !doc.documentElement) {
              return document;
            }

            // Set our document
            document = doc;
            docElem = doc.documentElement;

            // Support tests
            documentIsXML = isXML(doc);

            // Check if getElementsByTagName("*") returns only elements
            support.tagNameNoComments = assert(function (div) {
              div.appendChild(doc.createComment(""));
              return !div.getElementsByTagName("*").length;
            });

            // Check if attributes should be retrieved by attribute nodes
            support.attributes = assert(function (div) {
              div.innerHTML = "<select></select>";
              var type = typeof div.lastChild.getAttribute("multiple");
              // IE8 returns a string for some attributes even when not present
              return type !== "boolean" && type !== "string";
            });

            // Check if getElementsByClassName can be trusted
            support.getByClassName = assert(function (div) {
              // Opera can't find a second classname (in 9.6)
              div.innerHTML = "<div class='hidden e'></div><div class='hidden'></div>";
              if (!div.getElementsByClassName || !div.getElementsByClassName("e").length) {
                return false;
              }

              // Safari 3.2 caches class attributes and doesn't catch changes
              div.lastChild.className = "e";
              return div.getElementsByClassName("e").length === 2;
            });

            // Check if getElementById returns elements by name
            // Check if getElementsByName privileges form controls or returns elements by ID
            support.getByName = assert(function (div) {
              // Inject content
              div.id = expando + 0;
              div.innerHTML = "<a name='" + expando + "'></a><div name='" + expando + "'></div>";
              docElem.insertBefore(div, docElem.firstChild);

              // Test
              var pass = doc.getElementsByName &&
              // buggy browsers will return fewer than the correct 2
              doc.getElementsByName(expando).length === 2 +
              // buggy browsers will return more than the correct 0
              doc.getElementsByName(expando + 0).length;
              support.getIdNotName = !doc.getElementById(expando);

              // Cleanup
              docElem.removeChild(div);

              return pass;
            });

            // IE6/7 return modified attributes
            Expr.attrHandle = assert(function (div) {
              div.innerHTML = "<a href='#'></a>";
              return div.firstChild && typeof div.firstChild.getAttribute !== strundefined && div.firstChild.getAttribute("href") === "#";
            }) ? {} : {
              "href": function (elem) {
                return elem.getAttribute("href", 2);
              },
              "type": function (elem) {
                return elem.getAttribute("type");
              }
            };

            // ID find and filter
            if (support.getIdNotName) {
              Expr.find["ID"] = function (id, context) {
                if (typeof context.getElementById !== strundefined && !documentIsXML) {
                  var m = context.getElementById(id);
                  // Check parentNode to catch when Blackberry 4.6 returns
                  // nodes that are no longer in the document #6963
                  return m && m.parentNode ? [m] : [];
                }
              };
              Expr.filter["ID"] = function (id) {
                var attrId = id.replace(runescape, funescape);
                return function (elem) {
                  return elem.getAttribute("id") === attrId;
                };
              };
            } else {
              Expr.find["ID"] = function (id, context) {
                if (typeof context.getElementById !== strundefined && !documentIsXML) {
                  var m = context.getElementById(id);

                  return m ? m.id === id || typeof m.getAttributeNode !== strundefined && m.getAttributeNode("id").value === id ? [m] : undefined : [];
                }
              };
              Expr.filter["ID"] = function (id) {
                var attrId = id.replace(runescape, funescape);
                return function (elem) {
                  var node = typeof elem.getAttributeNode !== strundefined && elem.getAttributeNode("id");
                  return node && node.value === attrId;
                };
              };
            }

            // Tag
            Expr.find["TAG"] = support.tagNameNoComments ?
            function (tag, context) {
              if (typeof context.getElementsByTagName !== strundefined) {
                return context.getElementsByTagName(tag);
              }
            } : function (tag, context) {
              var elem, tmp = [],
                i = 0,
                results = context.getElementsByTagName(tag);

              // Filter out possible comments
              if (tag === "*") {
                while ((elem = results[i++])) {
                  if (elem.nodeType === 1) {
                    tmp.push(elem);
                  }
                }

                return tmp;
              }
              return results;
            };

            // Name
            Expr.find["NAME"] = support.getByName &&
            function (tag, context) {
              if (typeof context.getElementsByName !== strundefined) {
                return context.getElementsByName(name);
              }
            };

            // Class
            Expr.find["CLASS"] = support.getByClassName &&
            function (className, context) {
              if (typeof context.getElementsByClassName !== strundefined && !documentIsXML) {
                return context.getElementsByClassName(className);
              }
            };

            // QSA and matchesSelector support
            // matchesSelector(:active) reports false when true (IE9/Opera 11.5)
            rbuggyMatches = [];

            // qSa(:focus) reports false when true (Chrome 21),
            // no need to also add to buggyMatches since matches checks buggyQSA
            // A support test would require too much code (would include document ready)
            rbuggyQSA = [":focus"];

            if ((support.qsa = isNative(doc.querySelectorAll))) {
              // Build QSA regex
              // Regex strategy adopted from Diego Perini
              assert(function (div) {
                // Select is set to empty string on purpose
                // This is to test IE's treatment of not explictly
                // setting a boolean content attribute,
                // since its presence should be enough
                // http://bugs.jquery.com/ticket/12359
                div.innerHTML = "<select><option selected=''></option></select>";

                // IE8 - Some boolean attributes are not treated correctly
                if (!div.querySelectorAll("[selected]").length) {
                  rbuggyQSA.push("\\[" + whitespace + "*(?:checked|disabled|ismap|multiple|readonly|selected|value)");
                }

                // Webkit/Opera - :checked should return selected option elements
                // http://www.w3.org/TR/2011/REC-css3-selectors-20110929/#checked
                // IE8 throws error here and will not see later tests
                if (!div.querySelectorAll(":checked").length) {
                  rbuggyQSA.push(":checked");
                }
              });

              assert(function (div) {

                // Opera 10-12/IE8 - ^= $= *= and empty values
                // Should not select anything
                div.innerHTML = "<input type='hidden' i=''/>";
                if (div.querySelectorAll("[i^='']").length) {
                  rbuggyQSA.push("[*^$]=" + whitespace + "*(?:\"\"|'')");
                }

                // FF 3.5 - :enabled/:disabled and hidden elements (hidden elements are still enabled)
                // IE8 throws error here and will not see later tests
                if (!div.querySelectorAll(":enabled").length) {
                  rbuggyQSA.push(":enabled", ":disabled");
                }

                // Opera 10-11 does not throw on post-comma invalid pseudos
                div.querySelectorAll("*,:x");
                rbuggyQSA.push(",.*:");
              });
            }

            if ((support.matchesSelector = isNative((matches = docElem.matchesSelector || docElem.mozMatchesSelector || docElem.webkitMatchesSelector || docElem.oMatchesSelector || docElem.msMatchesSelector)))) {

              assert(function (div) {
                // Check to see if it's possible to do matchesSelector
                // on a disconnected node (IE 9)
                support.disconnectedMatch = matches.call(div, "div");

                // This should fail with an exception
                // Gecko does not error, returns false instead
                matches.call(div, "[s!='']:x");
                rbuggyMatches.push("!=", pseudos);
              });
            }

            rbuggyQSA = new RegExp(rbuggyQSA.join("|"));
            rbuggyMatches = new RegExp(rbuggyMatches.join("|"));

            // Element contains another
            // Purposefully does not implement inclusive descendent
            // As in, an element does not contain itself
            contains = isNative(docElem.contains) || docElem.compareDocumentPosition ?
            function (a, b) {
              var adown = a.nodeType === 9 ? a.documentElement : a,
                bup = b && b.parentNode;
              return a === bup || !! (bup && bup.nodeType === 1 && (
              adown.contains ? adown.contains(bup) : a.compareDocumentPosition && a.compareDocumentPosition(bup) & 16));
            } : function (a, b) {
              if (b) {
                while ((b = b.parentNode)) {
                  if (b === a) {
                    return true;
                  }
                }
              }
              return false;
            };

            // Document order sorting
            sortOrder = docElem.compareDocumentPosition ?
            function (a, b) {
              var compare;

              if (a === b) {
                hasDuplicate = true;
                return 0;
              }

              if ((compare = b.compareDocumentPosition && a.compareDocumentPosition && a.compareDocumentPosition(b))) {
                if (compare & 1 || a.parentNode && a.parentNode.nodeType === 11) {
                  if (a === doc || contains(preferredDoc, a)) {
                    return -1;
                  }
                  if (b === doc || contains(preferredDoc, b)) {
                    return 1;
                  }
                  return 0;
                }
                return compare & 4 ? -1 : 1;
              }

              return a.compareDocumentPosition ? -1 : 1;
            } : function (a, b) {
              var cur, i = 0,
                aup = a.parentNode,
                bup = b.parentNode,
                ap = [a],
                bp = [b];

              // Exit early if the nodes are identical
              if (a === b) {
                hasDuplicate = true;
                return 0;

                // Parentless nodes are either documents or disconnected
              } else if (!aup || !bup) {
                return a === doc ? -1 : b === doc ? 1 : aup ? -1 : bup ? 1 : 0;

                // If the nodes are siblings, we can do a quick check
              } else if (aup === bup) {
                return siblingCheck(a, b);
              }

              // Otherwise we need full lists of their ancestors for comparison
              cur = a;
              while ((cur = cur.parentNode)) {
                ap.unshift(cur);
              }
              cur = b;
              while ((cur = cur.parentNode)) {
                bp.unshift(cur);
              }

              // Walk down the tree looking for a discrepancy
              while (ap[i] === bp[i]) {
                i++;
              }

              return i ?
              // Do a sibling check if the nodes have a common ancestor
              siblingCheck(ap[i], bp[i]) :

              // Otherwise nodes in our document sort first
              ap[i] === preferredDoc ? -1 : bp[i] === preferredDoc ? 1 : 0;
            };

            // Always assume the presence of duplicates if sort doesn't
            // pass them to our comparison function (as in Google Chrome).
            hasDuplicate = false;
            [0, 0].sort(sortOrder);
            support.detectDuplicates = hasDuplicate;

            return document;
          };

          Sizzle.matches = function (expr, elements) {
            return Sizzle(expr, null, null, elements);
          };

          Sizzle.matchesSelector = function (elem, expr) {
            // Set document vars if needed
            if ((elem.ownerDocument || elem) !== document) {
              setDocument(elem);
            }

            // Make sure that attribute selectors are quoted
            expr = expr.replace(rattributeQuotes, "='$1']");

            // rbuggyQSA always contains :focus, so no need for an existence check
            if (support.matchesSelector && !documentIsXML && (!rbuggyMatches || !rbuggyMatches.test(expr)) && !rbuggyQSA.test(expr)) {
              try {
                var ret = matches.call(elem, expr);

                // IE 9's matchesSelector returns false on disconnected nodes
                if (ret || support.disconnectedMatch ||
                // As well, disconnected nodes are said to be in a document
                // fragment in IE 9
                elem.document && elem.document.nodeType !== 11) {
                  return ret;
                }
              } catch (e) {}
            }

            return Sizzle(expr, document, null, [elem]).length > 0;
          };

          Sizzle.contains = function (context, elem) {
            // Set document vars if needed
            if ((context.ownerDocument || context) !== document) {
              setDocument(context);
            }
            return contains(context, elem);
          };

          Sizzle.attr = function (elem, name) {
            var val;

            // Set document vars if needed
            if ((elem.ownerDocument || elem) !== document) {
              setDocument(elem);
            }

            if (!documentIsXML) {
              name = name.toLowerCase();
            }
            if ((val = Expr.attrHandle[name])) {
              return val(elem);
            }
            if (documentIsXML || support.attributes) {
              return elem.getAttribute(name);
            }
            return ((val = elem.getAttributeNode(name)) || elem.getAttribute(name)) && elem[name] === true ? name : val && val.specified ? val.value : null;
          };

          Sizzle.error = function (msg) {
            throw new Error("Syntax error, unrecognized expression: " + msg);
          };

          // Document sorting and removing duplicates
          Sizzle.uniqueSort = function (results) {
            var elem, duplicates = [],
              i = 1,
              j = 0;

            // Unless we *know* we can detect duplicates, assume their presence
            hasDuplicate = !support.detectDuplicates;
            results.sort(sortOrder);

            if (hasDuplicate) {
              for (;
              (elem = results[i]); i++) {
                if (elem === results[i - 1]) {
                  j = duplicates.push(i);
                }
              }
              while (j--) {
                results.splice(duplicates[j], 1);
              }
            }

            return results;
          };

          function siblingCheck(a, b) {
            var cur = b && a,
              diff = cur && (~b.sourceIndex || MAX_NEGATIVE) - (~a.sourceIndex || MAX_NEGATIVE);

            // Use IE sourceIndex if available on both nodes
            if (diff) {
              return diff;
            }

            // Check if b follows a
            if (cur) {
              while ((cur = cur.nextSibling)) {
                if (cur === b) {
                  return -1;
                }
              }
            }

            return a ? 1 : -1;
          }

          // Returns a function to use in pseudos for input types
          function createInputPseudo(type) {
            return function (elem) {
              var name = elem.nodeName.toLowerCase();
              return name === "input" && elem.type === type;
            };
          }

          // Returns a function to use in pseudos for buttons
          function createButtonPseudo(type) {
            return function (elem) {
              var name = elem.nodeName.toLowerCase();
              return (name === "input" || name === "button") && elem.type === type;
            };
          }

          // Returns a function to use in pseudos for positionals
          function createPositionalPseudo(fn) {
            return markFunction(function (argument) {
              argument = +argument;
              return markFunction(function (seed, matches) {
                var j, matchIndexes = fn([], seed.length, argument),
                  i = matchIndexes.length;

                // Match elements found at the specified indexes
                while (i--) {
                  if (seed[(j = matchIndexes[i])]) {
                    seed[j] = !(matches[j] = seed[j]);
                  }
                }
              });
            });
          }

          /**
           * Utility function for retrieving the text value of an array of DOM nodes
           * @param {Array|Element} elem
           */
          getText = Sizzle.getText = function (elem) {
            var node, ret = "",
              i = 0,
              nodeType = elem.nodeType;

            if (!nodeType) {
              // If no nodeType, this is expected to be an array
              for (;
              (node = elem[i]); i++) {
                // Do not traverse comment nodes
                ret += getText(node);
              }
            } else if (nodeType === 1 || nodeType === 9 || nodeType === 11) {
              // Use textContent for elements
              // innerText usage removed for consistency of new lines (see #11153)
              if (typeof elem.textContent === "string") {
                return elem.textContent;
              } else {
                // Traverse its children
                for (elem = elem.firstChild; elem; elem = elem.nextSibling) {
                  ret += getText(elem);
                }
              }
            } else if (nodeType === 3 || nodeType === 4) {
              return elem.nodeValue;
            }
            // Do not include comment or processing instruction nodes
            return ret;
          };

          Expr = Sizzle.selectors = {

            // Can be adjusted by the user
            cacheLength: 50,

            createPseudo: markFunction,

            match: matchExpr,

            find: {},

            relative: {
              ">": {
                dir: "parentNode",
                first: true
              },
              " ": {
                dir: "parentNode"
              },
              "+": {
                dir: "previousSibling",
                first: true
              },
              "~": {
                dir: "previousSibling"
              }
            },

            preFilter: {
              "ATTR": function (match) {
                match[1] = match[1].replace(runescape, funescape);

                // Move the given value to match[3] whether quoted or unquoted
                match[3] = (match[4] || match[5] || "").replace(runescape, funescape);

                if (match[2] === "~=") {
                  match[3] = " " + match[3] + " ";
                }

                return match.slice(0, 4);
              },

              "CHILD": function (match) {
                /* matches from matchExpr["CHILD"]
				1 type (only|nth|...)
				2 what (child|of-type)
				3 argument (even|odd|\d*|\d*n([+-]\d+)?|...)
				4 xn-component of xn+y argument ([+-]?\d*n|)
				5 sign of xn-component
				6 x of xn-component
				7 sign of y-component
				8 y of y-component
			*/
                match[1] = match[1].toLowerCase();

                if (match[1].slice(0, 3) === "nth") {
                  // nth-* requires argument
                  if (!match[3]) {
                    Sizzle.error(match[0]);
                  }

                  // numeric x and y parameters for Expr.filter.CHILD
                  // remember that false/true cast respectively to 0/1
                  match[4] = +(match[4] ? match[5] + (match[6] || 1) : 2 * (match[3] === "even" || match[3] === "odd"));
                  match[5] = +((match[7] + match[8]) || match[3] === "odd");

                  // other types prohibit arguments
                } else if (match[3]) {
                  Sizzle.error(match[0]);
                }

                return match;
              },

              "PSEUDO": function (match) {
                var excess, unquoted = !match[5] && match[2];

                if (matchExpr["CHILD"].test(match[0])) {
                  return null;
                }

                // Accept quoted arguments as-is
                if (match[4]) {
                  match[2] = match[4];

                  // Strip excess characters from unquoted arguments
                } else if (unquoted && rpseudo.test(unquoted) &&
                // Get excess from tokenize (recursively)
                (excess = tokenize(unquoted, true)) &&
                // advance to the next closing parenthesis
                (excess = unquoted.indexOf(")", unquoted.length - excess) - unquoted.length)) {

                  // excess is a negative index
                  match[0] = match[0].slice(0, excess);
                  match[2] = unquoted.slice(0, excess);
                }

                // Return only captures needed by the pseudo filter method (type and argument)
                return match.slice(0, 3);
              }
            },

            filter: {

              "TAG": function (nodeName) {
                if (nodeName === "*") {
                  return function () {
                    return true;
                  };
                }

                nodeName = nodeName.replace(runescape, funescape).toLowerCase();
                return function (elem) {
                  return elem.nodeName && elem.nodeName.toLowerCase() === nodeName;
                };
              },

              "CLASS": function (className) {
                var pattern = classCache[className + " "];

                return pattern || (pattern = new RegExp("(^|" + whitespace + ")" + className + "(" + whitespace + "|$)")) && classCache(className, function (elem) {
                  return pattern.test(elem.className || (typeof elem.getAttribute !== strundefined && elem.getAttribute("class")) || "");
                });
              },

              "ATTR": function (name, operator, check) {
                return function (elem) {
                  var result = Sizzle.attr(elem, name);

                  if (result == null) {
                    return operator === "!=";
                  }
                  if (!operator) {
                    return true;
                  }

                  result += "";

                  return operator === "=" ? result === check : operator === "!=" ? result !== check : operator === "^=" ? check && result.indexOf(check) === 0 : operator === "*=" ? check && result.indexOf(check) > -1 : operator === "$=" ? check && result.slice(-check.length) === check : operator === "~=" ? (" " + result + " ").indexOf(check) > -1 : operator === "|=" ? result === check || result.slice(0, check.length + 1) === check + "-" : false;
                };
              },

              "CHILD": function (type, what, argument, first, last) {
                var simple = type.slice(0, 3) !== "nth",
                  forward = type.slice(-4) !== "last",
                  ofType = what === "of-type";

                return first === 1 && last === 0 ?

                // Shortcut for :nth-*(n)
                function (elem) {
                  return !!elem.parentNode;
                } :

                function (elem, context, xml) {
                  var cache, outerCache, node, diff, nodeIndex, start, dir = simple !== forward ? "nextSibling" : "previousSibling",
                    parent = elem.parentNode,
                    name = ofType && elem.nodeName.toLowerCase(),
                    useCache = !xml && !ofType;

                  if (parent) {

                    // :(first|last|only)-(child|of-type)
                    if (simple) {
                      while (dir) {
                        node = elem;
                        while ((node = node[dir])) {
                          if (ofType ? node.nodeName.toLowerCase() === name : node.nodeType === 1) {
                            return false;
                          }
                        }
                        // Reverse direction for :only-* (if we haven't yet done so)
                        start = dir = type === "only" && !start && "nextSibling";
                      }
                      return true;
                    }

                    start = [forward ? parent.firstChild : parent.lastChild];

                    // non-xml :nth-child(...) stores cache data on `parent`
                    if (forward && useCache) {
                      // Seek `elem` from a previously-cached index
                      outerCache = parent[expando] || (parent[expando] = {});
                      cache = outerCache[type] || [];
                      nodeIndex = cache[0] === dirruns && cache[1];
                      diff = cache[0] === dirruns && cache[2];
                      node = nodeIndex && parent.childNodes[nodeIndex];

                      while ((node = ++nodeIndex && node && node[dir] ||

                      // Fallback to seeking `elem` from the start
                      (diff = nodeIndex = 0) || start.pop())) {

                        // When found, cache indexes on `parent` and break
                        if (node.nodeType === 1 && ++diff && node === elem) {
                          outerCache[type] = [dirruns, nodeIndex, diff];
                          break;
                        }
                      }

                      // Use previously-cached element index if available
                    } else if (useCache && (cache = (elem[expando] || (elem[expando] = {}))[type]) && cache[0] === dirruns) {
                      diff = cache[1];

                      // xml :nth-child(...) or :nth-last-child(...) or :nth(-last)?-of-type(...)
                    } else {
                      // Use the same loop as above to seek `elem` from the start
                      while ((node = ++nodeIndex && node && node[dir] || (diff = nodeIndex = 0) || start.pop())) {

                        if ((ofType ? node.nodeName.toLowerCase() === name : node.nodeType === 1) && ++diff) {
                          // Cache the index of each encountered element
                          if (useCache) {
                            (node[expando] || (node[expando] = {}))[type] = [dirruns, diff];
                          }

                          if (node === elem) {
                            break;
                          }
                        }
                      }
                    }

                    // Incorporate the offset, then check against cycle size
                    diff -= last;
                    return diff === first || (diff % first === 0 && diff / first >= 0);
                  }
                };
              },

              "PSEUDO": function (pseudo, argument) {
                // pseudo-class names are case-insensitive
                // http://www.w3.org/TR/selectors/#pseudo-classes
                // Prioritize by case sensitivity in case custom pseudos are added with uppercase letters
                // Remember that setFilters inherits from pseudos
                var args, fn = Expr.pseudos[pseudo] || Expr.setFilters[pseudo.toLowerCase()] || Sizzle.error("unsupported pseudo: " + pseudo);

                // The user may use createPseudo to indicate that
                // arguments are needed to create the filter function
                // just as Sizzle does
                if (fn[expando]) {
                  return fn(argument);
                }

                // But maintain support for old signatures
                if (fn.length > 1) {
                  args = [pseudo, pseudo, "", argument];
                  return Expr.setFilters.hasOwnProperty(pseudo.toLowerCase()) ? markFunction(function (seed, matches) {
                    var idx, matched = fn(seed, argument),
                      i = matched.length;
                    while (i--) {
                      idx = indexOf.call(seed, matched[i]);
                      seed[idx] = !(matches[idx] = matched[i]);
                    }
                  }) : function (elem) {
                    return fn(elem, 0, args);
                  };
                }

                return fn;
              }
            },

            pseudos: {
              // Potentially complex pseudos
              "not": markFunction(function (selector) {
                // Trim the selector passed to compile
                // to avoid treating leading and trailing
                // spaces as combinators
                var input = [],
                  results = [],
                  matcher = compile(selector.replace(rtrim, "$1"));

                return matcher[expando] ? markFunction(function (seed, matches, context, xml) {
                  var elem, unmatched = matcher(seed, null, xml, []),
                    i = seed.length;

                  // Match elements unmatched by `matcher`
                  while (i--) {
                    if ((elem = unmatched[i])) {
                      seed[i] = !(matches[i] = elem);
                    }
                  }
                }) : function (elem, context, xml) {
                  input[0] = elem;
                  matcher(input, null, xml, results);
                  return !results.pop();
                };
              }),

              "has": markFunction(function (selector) {
                return function (elem) {
                  return Sizzle(selector, elem).length > 0;
                };
              }),

              "contains": markFunction(function (text) {
                return function (elem) {
                  return (elem.textContent || elem.innerText || getText(elem)).indexOf(text) > -1;
                };
              }),

              // "Whether an element is represented by a :lang() selector
              // is based solely on the element's language value
              // being equal to the identifier C,
              // or beginning with the identifier C immediately followed by "-".
              // The matching of C against the element's language value is performed case-insensitively.
              // The identifier C does not have to be a valid language name."
              // http://www.w3.org/TR/selectors/#lang-pseudo
              "lang": markFunction(function (lang) {
                // lang value must be a valid identifider
                if (!ridentifier.test(lang || "")) {
                  Sizzle.error("unsupported lang: " + lang);
                }
                lang = lang.replace(runescape, funescape).toLowerCase();
                return function (elem) {
                  var elemLang;
                  do {
                    if ((elemLang = documentIsXML ? elem.getAttribute("xml:lang") || elem.getAttribute("lang") : elem.lang)) {

                      elemLang = elemLang.toLowerCase();
                      return elemLang === lang || elemLang.indexOf(lang + "-") === 0;
                    }
                  } while ((elem = elem.parentNode) && elem.nodeType === 1);
                  return false;
                };
              }),

              // Miscellaneous
              "target": function (elem) {
                var hash = window.location && window.location.hash;
                return hash && hash.slice(1) === elem.id;
              },

              "root": function (elem) {
                return elem === docElem;
              },

              "focus": function (elem) {
                return elem === document.activeElement && (!document.hasFocus || document.hasFocus()) && !! (elem.type || elem.href || ~elem.tabIndex);
              },

              // Boolean properties
              "enabled": function (elem) {
                return elem.disabled === false;
              },

              "disabled": function (elem) {
                return elem.disabled === true;
              },

              "checked": function (elem) {
                // In CSS3, :checked should return both checked and selected elements
                // http://www.w3.org/TR/2011/REC-css3-selectors-20110929/#checked
                var nodeName = elem.nodeName.toLowerCase();
                return (nodeName === "input" && !! elem.checked) || (nodeName === "option" && !! elem.selected);
              },

              "selected": function (elem) {
                // Accessing this property makes selected-by-default
                // options in Safari work properly
                if (elem.parentNode) {
                  elem.parentNode.selectedIndex;
                }

                return elem.selected === true;
              },

              // Contents
              "empty": function (elem) {
                // http://www.w3.org/TR/selectors/#empty-pseudo
                // :empty is only affected by element nodes and content nodes(including text(3), cdata(4)),
                //   not comment, processing instructions, or others
                // Thanks to Diego Perini for the nodeName shortcut
                //   Greater than "@" means alpha characters (specifically not starting with "#" or "?")
                for (elem = elem.firstChild; elem; elem = elem.nextSibling) {
                  if (elem.nodeName > "@" || elem.nodeType === 3 || elem.nodeType === 4) {
                    return false;
                  }
                }
                return true;
              },

              "parent": function (elem) {
                return !Expr.pseudos["empty"](elem);
              },

              // Element/input types
              "header": function (elem) {
                return rheader.test(elem.nodeName);
              },

              "input": function (elem) {
                return rinputs.test(elem.nodeName);
              },

              "button": function (elem) {
                var name = elem.nodeName.toLowerCase();
                return name === "input" && elem.type === "button" || name === "button";
              },

              "text": function (elem) {
                var attr;
                // IE6 and 7 will map elem.type to 'text' for new HTML5 types (search, etc)
                // use getAttribute instead to test this case
                return elem.nodeName.toLowerCase() === "input" && elem.type === "text" && ((attr = elem.getAttribute("type")) == null || attr.toLowerCase() === elem.type);
              },

              // Position-in-collection
              "first": createPositionalPseudo(function () {
                return [0];
              }),

              "last": createPositionalPseudo(function (matchIndexes, length) {
                return [length - 1];
              }),

              "eq": createPositionalPseudo(function (matchIndexes, length, argument) {
                return [argument < 0 ? argument + length : argument];
              }),

              "even": createPositionalPseudo(function (matchIndexes, length) {
                var i = 0;
                for (; i < length; i += 2) {
                  matchIndexes.push(i);
                }
                return matchIndexes;
              }),

              "odd": createPositionalPseudo(function (matchIndexes, length) {
                var i = 1;
                for (; i < length; i += 2) {
                  matchIndexes.push(i);
                }
                return matchIndexes;
              }),

              "lt": createPositionalPseudo(function (matchIndexes, length, argument) {
                var i = argument < 0 ? argument + length : argument;
                for (; --i >= 0;) {
                  matchIndexes.push(i);
                }
                return matchIndexes;
              }),

              "gt": createPositionalPseudo(function (matchIndexes, length, argument) {
                var i = argument < 0 ? argument + length : argument;
                for (; ++i < length;) {
                  matchIndexes.push(i);
                }
                return matchIndexes;
              })
            }
          };

          // Add button/input type pseudos
          for (i in {
            radio: true,
            checkbox: true,
            file: true,
            password: true,
            image: true
          }) {
            Expr.pseudos[i] = createInputPseudo(i);
          }
          for (i in {
            submit: true,
            reset: true
          }) {
            Expr.pseudos[i] = createButtonPseudo(i);
          }

          function tokenize(selector, parseOnly) {
            var matched, match, tokens, type, soFar, groups, preFilters, cached = tokenCache[selector + " "];

            if (cached) {
              return parseOnly ? 0 : cached.slice(0);
            }

            soFar = selector;
            groups = [];
            preFilters = Expr.preFilter;

            while (soFar) {

              // Comma and first run
              if (!matched || (match = rcomma.exec(soFar))) {
                if (match) {
                  // Don't consume trailing commas as valid
                  soFar = soFar.slice(match[0].length) || soFar;
                }
                groups.push(tokens = []);
              }

              matched = false;

              // Combinators
              if ((match = rcombinators.exec(soFar))) {
                matched = match.shift();
                tokens.push({
                  value: matched,
                  // Cast descendant combinators to space
                  type: match[0].replace(rtrim, " ")
                });
                soFar = soFar.slice(matched.length);
              }

              // Filters
              for (type in Expr.filter) {
                if ((match = matchExpr[type].exec(soFar)) && (!preFilters[type] || (match = preFilters[type](match)))) {
                  matched = match.shift();
                  tokens.push({
                    value: matched,
                    type: type,
                    matches: match
                  });
                  soFar = soFar.slice(matched.length);
                }
              }

              if (!matched) {
                break;
              }
            }

            // Return the length of the invalid excess
            // if we're just parsing
            // Otherwise, throw an error or return tokens
            return parseOnly ? soFar.length : soFar ? Sizzle.error(selector) :
            // Cache the tokens
            tokenCache(selector, groups).slice(0);
          }

          function toSelector(tokens) {
            var i = 0,
              len = tokens.length,
              selector = "";
            for (; i < len; i++) {
              selector += tokens[i].value;
            }
            return selector;
          }

          function addCombinator(matcher, combinator, base) {
            var dir = combinator.dir,
              checkNonElements = base && dir === "parentNode",
              doneName = done++;

            return combinator.first ?
            // Check against closest ancestor/preceding element
            function (elem, context, xml) {
              while ((elem = elem[dir])) {
                if (elem.nodeType === 1 || checkNonElements) {
                  return matcher(elem, context, xml);
                }
              }
            } :

            // Check against all ancestor/preceding elements
            function (elem, context, xml) {
              var data, cache, outerCache, dirkey = dirruns + " " + doneName;

              // We can't set arbitrary data on XML nodes, so they don't benefit from dir caching
              if (xml) {
                while ((elem = elem[dir])) {
                  if (elem.nodeType === 1 || checkNonElements) {
                    if (matcher(elem, context, xml)) {
                      return true;
                    }
                  }
                }
              } else {
                while ((elem = elem[dir])) {
                  if (elem.nodeType === 1 || checkNonElements) {
                    outerCache = elem[expando] || (elem[expando] = {});
                    if ((cache = outerCache[dir]) && cache[0] === dirkey) {
                      if ((data = cache[1]) === true || data === cachedruns) {
                        return data === true;
                      }
                    } else {
                      cache = outerCache[dir] = [dirkey];
                      cache[1] = matcher(elem, context, xml) || cachedruns;
                      if (cache[1] === true) {
                        return true;
                      }
                    }
                  }
                }
              }
            };
          }

          function elementMatcher(matchers) {
            return matchers.length > 1 ?
            function (elem, context, xml) {
              var i = matchers.length;
              while (i--) {
                if (!matchers[i](elem, context, xml)) {
                  return false;
                }
              }
              return true;
            } : matchers[0];
          }

          function condense(unmatched, map, filter, context, xml) {
            var elem, newUnmatched = [],
              i = 0,
              len = unmatched.length,
              mapped = map != null;

            for (; i < len; i++) {
              if ((elem = unmatched[i])) {
                if (!filter || filter(elem, context, xml)) {
                  newUnmatched.push(elem);
                  if (mapped) {
                    map.push(i);
                  }
                }
              }
            }

            return newUnmatched;
          }

          function setMatcher(preFilter, selector, matcher, postFilter, postFinder, postSelector) {
            if (postFilter && !postFilter[expando]) {
              postFilter = setMatcher(postFilter);
            }
            if (postFinder && !postFinder[expando]) {
              postFinder = setMatcher(postFinder, postSelector);
            }
            return markFunction(function (seed, results, context, xml) {
              var temp, i, elem, preMap = [],
                postMap = [],
                preexisting = results.length,

                // Get initial elements from seed or context
                elems = seed || multipleContexts(selector || "*", context.nodeType ? [context] : context, []),

                // Prefilter to get matcher input, preserving a map for seed-results synchronization
                matcherIn = preFilter && (seed || !selector) ? condense(elems, preMap, preFilter, context, xml) : elems,

                matcherOut = matcher ?
                // If we have a postFinder, or filtered seed, or non-seed postFilter or preexisting results,
                postFinder || (seed ? preFilter : preexisting || postFilter) ?

                // ...intermediate processing is necessary
                [] :

                // ...otherwise use results directly
                results : matcherIn;

              // Find primary matches
              if (matcher) {
                matcher(matcherIn, matcherOut, context, xml);
              }

              // Apply postFilter
              if (postFilter) {
                temp = condense(matcherOut, postMap);
                postFilter(temp, [], context, xml);

                // Un-match failing elements by moving them back to matcherIn
                i = temp.length;
                while (i--) {
                  if ((elem = temp[i])) {
                    matcherOut[postMap[i]] = !(matcherIn[postMap[i]] = elem);
                  }
                }
              }

              if (seed) {
                if (postFinder || preFilter) {
                  if (postFinder) {
                    // Get the final matcherOut by condensing this intermediate into postFinder contexts
                    temp = [];
                    i = matcherOut.length;
                    while (i--) {
                      if ((elem = matcherOut[i])) {
                        // Restore matcherIn since elem is not yet a final match
                        temp.push((matcherIn[i] = elem));
                      }
                    }
                    postFinder(null, (matcherOut = []), temp, xml);
                  }

                  // Move matched elements from seed to results to keep them synchronized
                  i = matcherOut.length;
                  while (i--) {
                    if ((elem = matcherOut[i]) && (temp = postFinder ? indexOf.call(seed, elem) : preMap[i]) > -1) {

                      seed[temp] = !(results[temp] = elem);
                    }
                  }
                }

                // Add elements to results, through postFinder if defined
              } else {
                matcherOut = condense(
                matcherOut === results ? matcherOut.splice(preexisting, matcherOut.length) : matcherOut);
                if (postFinder) {
                  postFinder(null, results, matcherOut, xml);
                } else {
                  push.apply(results, matcherOut);
                }
              }
            });
          }

          function matcherFromTokens(tokens) {
            var checkContext, matcher, j, len = tokens.length,
              leadingRelative = Expr.relative[tokens[0].type],
              implicitRelative = leadingRelative || Expr.relative[" "],
              i = leadingRelative ? 1 : 0,

              // The foundational matcher ensures that elements are reachable from top-level context(s)
              matchContext = addCombinator(function (elem) {
                return elem === checkContext;
              }, implicitRelative, true),
              matchAnyContext = addCombinator(function (elem) {
                return indexOf.call(checkContext, elem) > -1;
              }, implicitRelative, true),
              matchers = [function (elem, context, xml) {
                return (!leadingRelative && (xml || context !== outermostContext)) || (
                (checkContext = context).nodeType ? matchContext(elem, context, xml) : matchAnyContext(elem, context, xml));
              }];

            for (; i < len; i++) {
              if ((matcher = Expr.relative[tokens[i].type])) {
                matchers = [addCombinator(elementMatcher(matchers), matcher)];
              } else {
                matcher = Expr.filter[tokens[i].type].apply(null, tokens[i].matches);

                // Return special upon seeing a positional matcher
                if (matcher[expando]) {
                  // Find the next relative operator (if any) for proper handling
                  j = ++i;
                  for (; j < len; j++) {
                    if (Expr.relative[tokens[j].type]) {
                      break;
                    }
                  }
                  return setMatcher(
                  i > 1 && elementMatcher(matchers), i > 1 && toSelector(tokens.slice(0, i - 1)).replace(rtrim, "$1"), matcher, i < j && matcherFromTokens(tokens.slice(i, j)), j < len && matcherFromTokens((tokens = tokens.slice(j))), j < len && toSelector(tokens));
                }
                matchers.push(matcher);
              }
            }

            return elementMatcher(matchers);
          }

          function matcherFromGroupMatchers(elementMatchers, setMatchers) {
            // A counter to specify which element is currently being matched
            var matcherCachedRuns = 0,
              bySet = setMatchers.length > 0,
              byElement = elementMatchers.length > 0,
              superMatcher = function (seed, context, xml, results, expandContext) {
                var elem, j, matcher, setMatched = [],
                  matchedCount = 0,
                  i = "0",
                  unmatched = seed && [],
                  outermost = expandContext != null,
                  contextBackup = outermostContext,
                  // We must always have either seed elements or context
                  elems = seed || byElement && Expr.find["TAG"]("*", expandContext && context.parentNode || context),
                  // Use integer dirruns iff this is the outermost matcher
                  dirrunsUnique = (dirruns += contextBackup == null ? 1 : Math.random() || 0.1);

                if (outermost) {
                  outermostContext = context !== document && context;
                  cachedruns = matcherCachedRuns;
                }

                // Add elements passing elementMatchers directly to results
                // Keep `i` a string if there are no elements so `matchedCount` will be "00" below
                for (;
                (elem = elems[i]) != null; i++) {
                  if (byElement && elem) {
                    j = 0;
                    while ((matcher = elementMatchers[j++])) {
                      if (matcher(elem, context, xml)) {
                        results.push(elem);
                        break;
                      }
                    }
                    if (outermost) {
                      dirruns = dirrunsUnique;
                      cachedruns = ++matcherCachedRuns;
                    }
                  }

                  // Track unmatched elements for set filters
                  if (bySet) {
                    // They will have gone through all possible matchers
                    if ((elem = !matcher && elem)) {
                      matchedCount--;
                    }

                    // Lengthen the array for every element, matched or not
                    if (seed) {
                      unmatched.push(elem);
                    }
                  }
                }

                // Apply set filters to unmatched elements
                matchedCount += i;
                if (bySet && i !== matchedCount) {
                  j = 0;
                  while ((matcher = setMatchers[j++])) {
                    matcher(unmatched, setMatched, context, xml);
                  }

                  if (seed) {
                    // Reintegrate element matches to eliminate the need for sorting
                    if (matchedCount > 0) {
                      while (i--) {
                        if (!(unmatched[i] || setMatched[i])) {
                          setMatched[i] = pop.call(results);
                        }
                      }
                    }

                    // Discard index placeholder values to get only actual matches
                    setMatched = condense(setMatched);
                  }

                  // Add matches to results
                  push.apply(results, setMatched);

                  // Seedless set matches succeeding multiple successful matchers stipulate sorting
                  if (outermost && !seed && setMatched.length > 0 && (matchedCount + setMatchers.length) > 1) {

                    Sizzle.uniqueSort(results);
                  }
                }

                // Override manipulation of globals by nested matchers
                if (outermost) {
                  dirruns = dirrunsUnique;
                  outermostContext = contextBackup;
                }

                return unmatched;
              };

            return bySet ? markFunction(superMatcher) : superMatcher;
          }

          compile = Sizzle.compile = function (selector, group /* Internal Use Only */ ) {
            var i, setMatchers = [],
              elementMatchers = [],
              cached = compilerCache[selector + " "];

            if (!cached) {
              // Generate a function of recursive functions that can be used to check each element
              if (!group) {
                group = tokenize(selector);
              }
              i = group.length;
              while (i--) {
                cached = matcherFromTokens(group[i]);
                if (cached[expando]) {
                  setMatchers.push(cached);
                } else {
                  elementMatchers.push(cached);
                }
              }

              // Cache the compiled function
              cached = compilerCache(selector, matcherFromGroupMatchers(elementMatchers, setMatchers));
            }
            return cached;
          };

          function multipleContexts(selector, contexts, results) {
            var i = 0,
              len = contexts.length;
            for (; i < len; i++) {
              Sizzle(selector, contexts[i], results);
            }
            return results;
          }

          function select(selector, context, results, seed) {
            var i, tokens, token, type, find, match = tokenize(selector);

            if (!seed) {
              // Try to minimize operations if there is only one group
              if (match.length === 1) {

                // Take a shortcut and set the context if the root selector is an ID
                tokens = match[0] = match[0].slice(0);
                if (tokens.length > 2 && (token = tokens[0]).type === "ID" && context.nodeType === 9 && !documentIsXML && Expr.relative[tokens[1].type]) {

                  context = Expr.find["ID"](token.matches[0].replace(runescape, funescape), context)[0];
                  if (!context) {
                    return results;
                  }

                  selector = selector.slice(tokens.shift().value.length);
                }

                // Fetch a seed set for right-to-left matching
                i = matchExpr["needsContext"].test(selector) ? 0 : tokens.length;
                while (i--) {
                  token = tokens[i];

                  // Abort if we hit a combinator
                  if (Expr.relative[(type = token.type)]) {
                    break;
                  }
                  if ((find = Expr.find[type])) {
                    // Search, expanding context for leading sibling combinators
                    if ((seed = find(
                    token.matches[0].replace(runescape, funescape), rsibling.test(tokens[0].type) && context.parentNode || context))) {

                      // If seed is empty or no tokens remain, we can return early
                      tokens.splice(i, 1);
                      selector = seed.length && toSelector(tokens);
                      if (!selector) {
                        push.apply(results, slice.call(seed, 0));
                        return results;
                      }

                      break;
                    }
                  }
                }
              }
            }

            // Compile and execute a filtering function
            // Provide `match` to avoid retokenization if we modified the selector above
            compile(selector, match)(
            seed, context, documentIsXML, results, rsibling.test(selector));
            return results;
          }

          // Deprecated
          Expr.pseudos["nth"] = Expr.pseudos["eq"];

          // Easy API for creating new setFilters
          function setFilters() {}
          Expr.filters = setFilters.prototype = Expr.pseudos;
          Expr.setFilters = new setFilters();

          // Initialize with the default document
          setDocument();

          // Override sizzle attribute retrieval
          Sizzle.attr = jQuery.attr;
          jQuery.find = Sizzle;
          jQuery.expr = Sizzle.selectors;
          jQuery.expr[":"] = jQuery.expr.pseudos;
          jQuery.unique = Sizzle.uniqueSort;
          jQuery.text = Sizzle.getText;
          jQuery.isXMLDoc = Sizzle.isXML;
          jQuery.contains = Sizzle.contains;


        })(window);
        var runtil = /Until$/,
          rparentsprev = /^(?:parents|prev(?:Until|All))/,
          isSimple = /^.[^:#\[\.,]*$/,
          rneedsContext = jQuery.expr.match.needsContext,
          // methods guaranteed to produce a unique set when starting from a unique set
          guaranteedUnique = {
            children: true,
            contents: true,
            next: true,
            prev: true
          };

        jQuery.fn.extend({
          find: function (selector) {
            var i, ret, self, len = this.length;

            if (typeof selector !== "string") {
              self = this;
              return this.pushStack(jQuery(selector).filter(function () {
                for (i = 0; i < len; i++) {
                  if (jQuery.contains(self[i], this)) {
                    return true;
                  }
                }
              }));
            }

            ret = [];
            for (i = 0; i < len; i++) {
              jQuery.find(selector, this[i], ret);
            }

            // Needed because $( selector, context ) becomes $( context ).find( selector )
            ret = this.pushStack(len > 1 ? jQuery.unique(ret) : ret);
            ret.selector = (this.selector ? this.selector + " " : "") + selector;
            return ret;
          },

          has: function (target) {
            var i, targets = jQuery(target, this),
              len = targets.length;

            return this.filter(function () {
              for (i = 0; i < len; i++) {
                if (jQuery.contains(this, targets[i])) {
                  return true;
                }
              }
            });
          },

          not: function (selector) {
            return this.pushStack(winnow(this, selector, false));
          },

          filter: function (selector) {
            return this.pushStack(winnow(this, selector, true));
          },

          is: function (selector) {
            return !!selector && (
            typeof selector === "string" ?
            // If this is a positional/relative selector, check membership in the returned set
            // so $("p:first").is("p:last") won't return true for a doc with two "p".
            rneedsContext.test(selector) ? jQuery(selector, this.context).index(this[0]) >= 0 : jQuery.filter(selector, this).length > 0 : this.filter(selector).length > 0);
          },

          closest: function (selectors, context) {
            var cur, i = 0,
              l = this.length,
              ret = [],
              pos = rneedsContext.test(selectors) || typeof selectors !== "string" ? jQuery(selectors, context || this.context) : 0;

            for (; i < l; i++) {
              cur = this[i];

              while (cur && cur.ownerDocument && cur !== context && cur.nodeType !== 11) {
                if (pos ? pos.index(cur) > -1 : jQuery.find.matchesSelector(cur, selectors)) {
                  ret.push(cur);
                  break;
                }
                cur = cur.parentNode;
              }
            }

            return this.pushStack(ret.length > 1 ? jQuery.unique(ret) : ret);
          },

          // Determine the position of an element within
          // the matched set of elements
          index: function (elem) {

            // No argument, return index in parent
            if (!elem) {
              return (this[0] && this[0].parentNode) ? this.first().prevAll().length : -1;
            }

            // index in selector
            if (typeof elem === "string") {
              return jQuery.inArray(this[0], jQuery(elem));
            }

            // Locate the position of the desired element
            return jQuery.inArray(
            // If it receives a jQuery object, the first element is used
            elem.jquery ? elem[0] : elem, this);
          },

          add: function (selector, context) {
            var set = typeof selector === "string" ? jQuery(selector, context) : jQuery.makeArray(selector && selector.nodeType ? [selector] : selector),
              all = jQuery.merge(this.get(), set);

            return this.pushStack(jQuery.unique(all));
          },

          addBack: function (selector) {
            return this.add(selector == null ? this.prevObject : this.prevObject.filter(selector));
          }
        });

        jQuery.fn.andSelf = jQuery.fn.addBack;

        function sibling(cur, dir) {
          do {
            cur = cur[dir];
          } while (cur && cur.nodeType !== 1);

          return cur;
        }

        jQuery.each({
          parent: function (elem) {
            var parent = elem.parentNode;
            return parent && parent.nodeType !== 11 ? parent : null;
          },
          parents: function (elem) {
            return jQuery.dir(elem, "parentNode");
          },
          parentsUntil: function (elem, i, until) {
            return jQuery.dir(elem, "parentNode", until);
          },
          next: function (elem) {
            return sibling(elem, "nextSibling");
          },
          prev: function (elem) {
            return sibling(elem, "previousSibling");
          },
          nextAll: function (elem) {
            return jQuery.dir(elem, "nextSibling");
          },
          prevAll: function (elem) {
            return jQuery.dir(elem, "previousSibling");
          },
          nextUntil: function (elem, i, until) {
            return jQuery.dir(elem, "nextSibling", until);
          },
          prevUntil: function (elem, i, until) {
            return jQuery.dir(elem, "previousSibling", until);
          },
          siblings: function (elem) {
            return jQuery.sibling((elem.parentNode || {}).firstChild, elem);
          },
          children: function (elem) {
            return jQuery.sibling(elem.firstChild);
          },
          contents: function (elem) {
            return jQuery.nodeName(elem, "iframe") ? elem.contentDocument || elem.contentWindow.document : jQuery.merge([], elem.childNodes);
          }
        }, function (name, fn) {
          jQuery.fn[name] = function (until, selector) {
            var ret = jQuery.map(this, fn, until);

            if (!runtil.test(name)) {
              selector = until;
            }

            if (selector && typeof selector === "string") {
              ret = jQuery.filter(selector, ret);
            }

            ret = this.length > 1 && !guaranteedUnique[name] ? jQuery.unique(ret) : ret;

            if (this.length > 1 && rparentsprev.test(name)) {
              ret = ret.reverse();
            }

            return this.pushStack(ret);
          };
        });

        jQuery.extend({
          filter: function (expr, elems, not) {
            if (not) {
              expr = ":not(" + expr + ")";
            }

            return elems.length === 1 ? jQuery.find.matchesSelector(elems[0], expr) ? [elems[0]] : [] : jQuery.find.matches(expr, elems);
          },

          dir: function (elem, dir, until) {
            var matched = [],
              cur = elem[dir];

            while (cur && cur.nodeType !== 9 && (until === undefined || cur.nodeType !== 1 || !jQuery(cur).is(until))) {
              if (cur.nodeType === 1) {
                matched.push(cur);
              }
              cur = cur[dir];
            }
            return matched;
          },

          sibling: function (n, elem) {
            var r = [];

            for (; n; n = n.nextSibling) {
              if (n.nodeType === 1 && n !== elem) {
                r.push(n);
              }
            }

            return r;
          }
        });

        // Implement the identical functionality for filter and not
        function winnow(elements, qualifier, keep) {

          // Can't pass null or undefined to indexOf in Firefox 4
          // Set to 0 to skip string check
          qualifier = qualifier || 0;

          if (jQuery.isFunction(qualifier)) {
            return jQuery.grep(elements, function (elem, i) {
              var retVal = !! qualifier.call(elem, i, elem);
              return retVal === keep;
            });

          } else if (qualifier.nodeType) {
            return jQuery.grep(elements, function (elem) {
              return (elem === qualifier) === keep;
            });

          } else if (typeof qualifier === "string") {
            var filtered = jQuery.grep(elements, function (elem) {
              return elem.nodeType === 1;
            });

            if (isSimple.test(qualifier)) {
              return jQuery.filter(qualifier, filtered, !keep);
            } else {
              qualifier = jQuery.filter(qualifier, filtered);
            }
          }

          return jQuery.grep(elements, function (elem) {
            return (jQuery.inArray(elem, qualifier) >= 0) === keep;
          });
        }

        function createSafeFragment(document) {
          var list = nodeNames.split("|"),
            safeFrag = document.createDocumentFragment();

          if (safeFrag.createElement) {
            while (list.length) {
              safeFrag.createElement(
              list.pop());
            }
          }
          return safeFrag;
        }

        var nodeNames = "abbr|article|aside|audio|bdi|canvas|data|datalist|details|figcaption|figure|footer|" + "header|hgroup|mark|meter|nav|output|progress|section|summary|time|video",
          rinlinejQuery = / jQuery\d+="(?:null|\d+)"/g,
          rnoshimcache = new RegExp("<(?:" + nodeNames + ")[\\s/>]", "i"),
          rleadingWhitespace = /^\s+/,
          rxhtmlTag = /<(?!area|br|col|embed|hr|img|input|link|meta|param)(([\w:]+)[^>]*)\/>/gi,
          rtagName = /<([\w:]+)/,
          rtbody = /<tbody/i,
          rhtml = /<|&#?\w+;/,
          rnoInnerhtml = /<(?:script|style|link)/i,
          manipulation_rcheckableType = /^(?:checkbox|radio)$/i,
          // checked="checked" or checked
          rchecked = /checked\s*(?:[^=]|=\s*.checked.)/i,
          rscriptType = /^$|\/(?:java|ecma)script/i,
          rscriptTypeMasked = /^true\/(.*)/,
          rcleanScript = /^\s*<!(?:\[CDATA\[|--)|(?:\]\]|--)>\s*$/g,

          // We have to close these tags to support XHTML (#13200)
          wrapMap = {
            option: [1, "<select multiple='multiple'>", "</select>"],
            legend: [1, "<fieldset>", "</fieldset>"],
            area: [1, "<map>", "</map>"],
            param: [1, "<object>", "</object>"],
            thead: [1, "<table>", "</table>"],
            tr: [2, "<table><tbody>", "</tbody></table>"],
            col: [2, "<table><tbody></tbody><colgroup>", "</colgroup></table>"],
            td: [3, "<table><tbody><tr>", "</tr></tbody></table>"],

            // IE6-8 can't serialize link, script, style, or any html5 (NoScope) tags,
            // unless wrapped in a div with non-breaking characters in front of it.
            _default: jQuery.support.htmlSerialize ? [0, "", ""] : [1, "X<div>", "</div>"]
          },
          safeFragment = createSafeFragment(document),
          fragmentDiv = safeFragment.appendChild(document.createElement("div"));

        wrapMap.optgroup = wrapMap.option;
        wrapMap.tbody = wrapMap.tfoot = wrapMap.colgroup = wrapMap.caption = wrapMap.thead;
        wrapMap.th = wrapMap.td;

        jQuery.fn.extend({
          text: function (value) {
            return jQuery.access(this, function (value) {
              return value === undefined ? jQuery.text(this) : this.empty().append((this[0] && this[0].ownerDocument || document).createTextNode(value));
            }, null, value, arguments.length);
          },

          wrapAll: function (html) {
            if (jQuery.isFunction(html)) {
              return this.each(function (i) {
                jQuery(this).wrapAll(html.call(this, i));
              });
            }

            if (this[0]) {
              // The elements to wrap the target around
              var wrap = jQuery(html, this[0].ownerDocument).eq(0).clone(true);

              if (this[0].parentNode) {
                wrap.insertBefore(this[0]);
              }

              wrap.map(function () {
                var elem = this;

                while (elem.firstChild && elem.firstChild.nodeType === 1) {
                  elem = elem.firstChild;
                }

                return elem;
              }).append(this);
            }

            return this;
          },

          wrapInner: function (html) {
            if (jQuery.isFunction(html)) {
              return this.each(function (i) {
                jQuery(this).wrapInner(html.call(this, i));
              });
            }

            return this.each(function () {
              var self = jQuery(this),
                contents = self.contents();

              if (contents.length) {
                contents.wrapAll(html);

              } else {
                self.append(html);
              }
            });
          },

          wrap: function (html) {
            var isFunction = jQuery.isFunction(html);

            return this.each(function (i) {
              jQuery(this).wrapAll(isFunction ? html.call(this, i) : html);
            });
          },

          unwrap: function () {
            return this.parent().each(function () {
              if (!jQuery.nodeName(this, "body")) {
                jQuery(this).replaceWith(this.childNodes);
              }
            }).end();
          },

          append: function () {
            return this.domManip(arguments, true, function (elem) {
              if (this.nodeType === 1 || this.nodeType === 11 || this.nodeType === 9) {
                this.appendChild(elem);
              }
            });
          },

          prepend: function () {
            return this.domManip(arguments, true, function (elem) {
              if (this.nodeType === 1 || this.nodeType === 11 || this.nodeType === 9) {
                this.insertBefore(elem, this.firstChild);
              }
            });
          },

          before: function () {
            return this.domManip(arguments, false, function (elem) {
              if (this.parentNode) {
                this.parentNode.insertBefore(elem, this);
              }
            });
          },

          after: function () {
            return this.domManip(arguments, false, function (elem) {
              if (this.parentNode) {
                this.parentNode.insertBefore(elem, this.nextSibling);
              }
            });
          },

          // keepData is for internal use only--do not document
          remove: function (selector, keepData) {
            var elem, i = 0;

            for (;
            (elem = this[i]) != null; i++) {
              if (!selector || jQuery.filter(selector, [elem]).length > 0) {
                if (!keepData && elem.nodeType === 1) {
                  jQuery.cleanData(getAll(elem));
                }

                if (elem.parentNode) {
                  if (keepData && jQuery.contains(elem.ownerDocument, elem)) {
                    setGlobalEval(getAll(elem, "script"));
                  }
                  elem.parentNode.removeChild(elem);
                }
              }
            }

            return this;
          },

          empty: function () {
            var elem, i = 0;

            for (;
            (elem = this[i]) != null; i++) {
              // Remove element nodes and prevent memory leaks
              if (elem.nodeType === 1) {
                jQuery.cleanData(getAll(elem, false));
              }

              // Remove any remaining nodes
              while (elem.firstChild) {
                elem.removeChild(elem.firstChild);
              }

              // If this is a select, ensure that it displays empty (#12336)
              // Support: IE<9
              if (elem.options && jQuery.nodeName(elem, "select")) {
                elem.options.length = 0;
              }
            }

            return this;
          },

          clone: function (dataAndEvents, deepDataAndEvents) {
            dataAndEvents = dataAndEvents == null ? false : dataAndEvents;
            deepDataAndEvents = deepDataAndEvents == null ? dataAndEvents : deepDataAndEvents;

            return this.map(function () {
              return jQuery.clone(this, dataAndEvents, deepDataAndEvents);
            });
          },

          html: function (value) {
            return jQuery.access(this, function (value) {
              var elem = this[0] || {},
                i = 0,
                l = this.length;

              if (value === undefined) {
                return elem.nodeType === 1 ? elem.innerHTML.replace(rinlinejQuery, "") : undefined;
              }

              // See if we can take a shortcut and just use innerHTML
              if (typeof value === "string" && !rnoInnerhtml.test(value) && (jQuery.support.htmlSerialize || !rnoshimcache.test(value)) && (jQuery.support.leadingWhitespace || !rleadingWhitespace.test(value)) && !wrapMap[(rtagName.exec(value) || ["", ""])[1].toLowerCase()]) {

                value = value.replace(rxhtmlTag, "<$1></$2>");

                try {
                  for (; i < l; i++) {
                    // Remove element nodes and prevent memory leaks
                    elem = this[i] || {};
                    if (elem.nodeType === 1) {
                      jQuery.cleanData(getAll(elem, false));
                      elem.innerHTML = value;
                    }
                  }

                  elem = 0;

                  // If using innerHTML throws an exception, use the fallback method
                } catch (e) {}
              }

              if (elem) {
                this.empty().append(value);
              }
            }, null, value, arguments.length);
          },

          replaceWith: function (value) {
            var isFunc = jQuery.isFunction(value);

            // Make sure that the elements are removed from the DOM before they are inserted
            // this can help fix replacing a parent with child elements
            if (!isFunc && typeof value !== "string") {
              value = jQuery(value).not(this).detach();
            }

            return this.domManip([value], true, function (elem) {
              var next = this.nextSibling,
                parent = this.parentNode;

              if (parent) {
                jQuery(this).remove();
                parent.insertBefore(elem, next);
              }
            });
          },

          detach: function (selector) {
            return this.remove(selector, true);
          },

          domManip: function (args, table, callback) {

            // Flatten any nested arrays
            args = core_concat.apply([], args);

            var first, node, hasScripts, scripts, doc, fragment, i = 0,
              l = this.length,
              set = this,
              iNoClone = l - 1,
              value = args[0],
              isFunction = jQuery.isFunction(value);

            // We can't cloneNode fragments that contain checked, in WebKit
            if (isFunction || !(l <= 1 || typeof value !== "string" || jQuery.support.checkClone || !rchecked.test(value))) {
              return this.each(function (index) {
                var self = set.eq(index);
                if (isFunction) {
                  args[0] = value.call(this, index, table ? self.html() : undefined);
                }
                self.domManip(args, table, callback);
              });
            }

            if (l) {
              fragment = jQuery.buildFragment(args, this[0].ownerDocument, false, this);
              first = fragment.firstChild;

              if (fragment.childNodes.length === 1) {
                fragment = first;
              }

              if (first) {
                table = table && jQuery.nodeName(first, "tr");
                scripts = jQuery.map(getAll(fragment, "script"), disableScript);
                hasScripts = scripts.length;

                // Use the original fragment for the last item instead of the first because it can end up
                // being emptied incorrectly in certain situations (#8070).
                for (; i < l; i++) {
                  node = fragment;

                  if (i !== iNoClone) {
                    node = jQuery.clone(node, true, true);

                    // Keep references to cloned scripts for later restoration
                    if (hasScripts) {
                      jQuery.merge(scripts, getAll(node, "script"));
                    }
                  }

                  callback.call(
                  table && jQuery.nodeName(this[i], "table") ? findOrAppend(this[i], "tbody") : this[i], node, i);
                }

                if (hasScripts) {
                  doc = scripts[scripts.length - 1].ownerDocument;

                  // Reenable scripts
                  jQuery.map(scripts, restoreScript);

                  // Evaluate executable scripts on first document insertion
                  for (i = 0; i < hasScripts; i++) {
                    node = scripts[i];
                    if (rscriptType.test(node.type || "") && !jQuery._data(node, "globalEval") && jQuery.contains(doc, node)) {

                      if (node.src) {
                        // Hope ajax is available...
                        jQuery.ajax({
                          url: node.src,
                          type: "GET",
                          dataType: "script",
                          async: false,
                          global: false,
                          "throws": true
                        });
                      } else {
                        jQuery.globalEval((node.text || node.textContent || node.innerHTML || "").replace(rcleanScript, ""));
                      }
                    }
                  }
                }

                // Fix #11809: Avoid leaking memory
                fragment = first = null;
              }
            }

            return this;
          }
        });

        function findOrAppend(elem, tag) {
          return elem.getElementsByTagName(tag)[0] || elem.appendChild(elem.ownerDocument.createElement(tag));
        }

        // Replace/restore the type attribute of script elements for safe DOM manipulation
        function disableScript(elem) {
          var attr = elem.getAttributeNode("type");
          elem.type = (attr && attr.specified) + "/" + elem.type;
          return elem;
        }

        function restoreScript(elem) {
          var match = rscriptTypeMasked.exec(elem.type);
          if (match) {
            elem.type = match[1];
          } else {
            elem.removeAttribute("type");
          }
          return elem;
        }

        // Mark scripts as having already been evaluated
        function setGlobalEval(elems, refElements) {
          var elem, i = 0;
          for (;
          (elem = elems[i]) != null; i++) {
            jQuery._data(elem, "globalEval", !refElements || jQuery._data(refElements[i], "globalEval"));
          }
        }

        function cloneCopyEvent(src, dest) {

          if (dest.nodeType !== 1 || !jQuery.hasData(src)) {
            return;
          }

          var type, i, l, oldData = jQuery._data(src),
            curData = jQuery._data(dest, oldData),
            events = oldData.events;

          if (events) {
            delete curData.handle;
            curData.events = {};

            for (type in events) {
              for (i = 0, l = events[type].length; i < l; i++) {
                jQuery.event.add(dest, type, events[type][i]);
              }
            }
          }

          // make the cloned public data object a copy from the original
          if (curData.data) {
            curData.data = jQuery.extend({}, curData.data);
          }
        }

        function fixCloneNodeIssues(src, dest) {
          var nodeName, e, data;

          // We do not need to do anything for non-Elements
          if (dest.nodeType !== 1) {
            return;
          }

          nodeName = dest.nodeName.toLowerCase();

          // IE6-8 copies events bound via attachEvent when using cloneNode.
          if (!jQuery.support.noCloneEvent && dest[jQuery.expando]) {
            data = jQuery._data(dest);

            for (e in data.events) {
              jQuery.removeEvent(dest, e, data.handle);
            }

            // Event data gets referenced instead of copied if the expando gets copied too
            dest.removeAttribute(jQuery.expando);
          }

          // IE blanks contents when cloning scripts, and tries to evaluate newly-set text
          if (nodeName === "script" && dest.text !== src.text) {
            disableScript(dest).text = src.text;
            restoreScript(dest);

            // IE6-10 improperly clones children of object elements using classid.
            // IE10 throws NoModificationAllowedError if parent is null, #12132.
          } else if (nodeName === "object") {
            if (dest.parentNode) {
              dest.outerHTML = src.outerHTML;
            }

            // This path appears unavoidable for IE9. When cloning an object
            // element in IE9, the outerHTML strategy above is not sufficient.
            // If the src has innerHTML and the destination does not,
            // copy the src.innerHTML into the dest.innerHTML. #10324
            if (jQuery.support.html5Clone && (src.innerHTML && !jQuery.trim(dest.innerHTML))) {
              dest.innerHTML = src.innerHTML;
            }

          } else if (nodeName === "input" && manipulation_rcheckableType.test(src.type)) {
            // IE6-8 fails to persist the checked state of a cloned checkbox
            // or radio button. Worse, IE6-7 fail to give the cloned element
            // a checked appearance if the defaultChecked value isn't also set
            dest.defaultChecked = dest.checked = src.checked;

            // IE6-7 get confused and end up setting the value of a cloned
            // checkbox/radio button to an empty string instead of "on"
            if (dest.value !== src.value) {
              dest.value = src.value;
            }

            // IE6-8 fails to return the selected option to the default selected
            // state when cloning options
          } else if (nodeName === "option") {
            dest.defaultSelected = dest.selected = src.defaultSelected;

            // IE6-8 fails to set the defaultValue to the correct value when
            // cloning other types of input fields
          } else if (nodeName === "input" || nodeName === "textarea") {
            dest.defaultValue = src.defaultValue;
          }
        }

        jQuery.each({
          appendTo: "append",
          prependTo: "prepend",
          insertBefore: "before",
          insertAfter: "after",
          replaceAll: "replaceWith"
        }, function (name, original) {
          jQuery.fn[name] = function (selector) {
            var elems, i = 0,
              ret = [],
              insert = jQuery(selector),
              last = insert.length - 1;

            for (; i <= last; i++) {
              elems = i === last ? this : this.clone(true);
              jQuery(insert[i])[original](elems);

              // Modern browsers can apply jQuery collections as arrays, but oldIE needs a .get()
              core_push.apply(ret, elems.get());
            }

            return this.pushStack(ret);
          };
        });

        function getAll(context, tag) {
          var elems, elem, i = 0,
            found = typeof context.getElementsByTagName !== core_strundefined ? context.getElementsByTagName(tag || "*") : typeof context.querySelectorAll !== core_strundefined ? context.querySelectorAll(tag || "*") : undefined;

          if (!found) {
            for (found = [], elems = context.childNodes || context;
            (elem = elems[i]) != null; i++) {
              if (!tag || jQuery.nodeName(elem, tag)) {
                found.push(elem);
              } else {
                jQuery.merge(found, getAll(elem, tag));
              }
            }
          }

          return tag === undefined || tag && jQuery.nodeName(context, tag) ? jQuery.merge([context], found) : found;
        }

        // Used in buildFragment, fixes the defaultChecked property
        function fixDefaultChecked(elem) {
          if (manipulation_rcheckableType.test(elem.type)) {
            elem.defaultChecked = elem.checked;
          }
        }

        jQuery.extend({
          clone: function (elem, dataAndEvents, deepDataAndEvents) {
            var destElements, node, clone, i, srcElements, inPage = jQuery.contains(elem.ownerDocument, elem);

            if (jQuery.support.html5Clone || jQuery.isXMLDoc(elem) || !rnoshimcache.test("<" + elem.nodeName + ">")) {
              clone = elem.cloneNode(true);

              // IE<=8 does not properly clone detached, unknown element nodes
            } else {
              fragmentDiv.innerHTML = elem.outerHTML;
              fragmentDiv.removeChild(clone = fragmentDiv.firstChild);
            }

            if ((!jQuery.support.noCloneEvent || !jQuery.support.noCloneChecked) && (elem.nodeType === 1 || elem.nodeType === 11) && !jQuery.isXMLDoc(elem)) {

              // We eschew Sizzle here for performance reasons: http://jsperf.com/getall-vs-sizzle/2
              destElements = getAll(clone);
              srcElements = getAll(elem);

              // Fix all IE cloning issues
              for (i = 0;
              (node = srcElements[i]) != null; ++i) {
                // Ensure that the destination node is not null; Fixes #9587
                if (destElements[i]) {
                  fixCloneNodeIssues(node, destElements[i]);
                }
              }
            }

            // Copy the events from the original to the clone
            if (dataAndEvents) {
              if (deepDataAndEvents) {
                srcElements = srcElements || getAll(elem);
                destElements = destElements || getAll(clone);

                for (i = 0;
                (node = srcElements[i]) != null; i++) {
                  cloneCopyEvent(node, destElements[i]);
                }
              } else {
                cloneCopyEvent(elem, clone);
              }
            }

            // Preserve script evaluation history
            destElements = getAll(clone, "script");
            if (destElements.length > 0) {
              setGlobalEval(destElements, !inPage && getAll(elem, "script"));
            }

            destElements = srcElements = node = null;

            // Return the cloned set
            return clone;
          },

          buildFragment: function (elems, context, scripts, selection) {
            var j, elem, contains, tmp, tag, tbody, wrap, l = elems.length,

              // Ensure a safe fragment
              safe = createSafeFragment(context),

              nodes = [],
              i = 0;

            for (; i < l; i++) {
              elem = elems[i];

              if (elem || elem === 0) {

                // Add nodes directly
                if (jQuery.type(elem) === "object") {
                  jQuery.merge(nodes, elem.nodeType ? [elem] : elem);

                  // Convert non-html into a text node
                } else if (!rhtml.test(elem)) {
                  nodes.push(context.createTextNode(elem));

                  // Convert html into DOM nodes
                } else {
                  tmp = tmp || safe.appendChild(context.createElement("div"));

                  // Deserialize a standard representation
                  tag = (rtagName.exec(elem) || ["", ""])[1].toLowerCase();
                  wrap = wrapMap[tag] || wrapMap._default;

                  tmp.innerHTML = wrap[1] + elem.replace(rxhtmlTag, "<$1></$2>") + wrap[2];

                  // Descend through wrappers to the right content
                  j = wrap[0];
                  while (j--) {
                    tmp = tmp.lastChild;
                  }

                  // Manually add leading whitespace removed by IE
                  if (!jQuery.support.leadingWhitespace && rleadingWhitespace.test(elem)) {
                    nodes.push(context.createTextNode(rleadingWhitespace.exec(elem)[0]));
                  }

                  // Remove IE's autoinserted <tbody> from table fragments
                  if (!jQuery.support.tbody) {

                    // String was a <table>, *may* have spurious <tbody>
                    elem = tag === "table" && !rtbody.test(elem) ? tmp.firstChild :

                    // String was a bare <thead> or <tfoot>
                    wrap[1] === "<table>" && !rtbody.test(elem) ? tmp : 0;

                    j = elem && elem.childNodes.length;
                    while (j--) {
                      if (jQuery.nodeName((tbody = elem.childNodes[j]), "tbody") && !tbody.childNodes.length) {
                        elem.removeChild(tbody);
                      }
                    }
                  }

                  jQuery.merge(nodes, tmp.childNodes);

                  // Fix #12392 for WebKit and IE > 9
                  tmp.textContent = "";

                  // Fix #12392 for oldIE
                  while (tmp.firstChild) {
                    tmp.removeChild(tmp.firstChild);
                  }

                  // Remember the top-level container for proper cleanup
                  tmp = safe.lastChild;
                }
              }
            }

            // Fix #11356: Clear elements from fragment
            if (tmp) {
              safe.removeChild(tmp);
            }

            // Reset defaultChecked for any radios and checkboxes
            // about to be appended to the DOM in IE 6/7 (#8060)
            if (!jQuery.support.appendChecked) {
              jQuery.grep(getAll(nodes, "input"), fixDefaultChecked);
            }

            i = 0;
            while ((elem = nodes[i++])) {

              // #4087 - If origin and destination elements are the same, and this is
              // that element, do not do anything
              if (selection && jQuery.inArray(elem, selection) !== -1) {
                continue;
              }

              contains = jQuery.contains(elem.ownerDocument, elem);

              // Append to fragment
              tmp = getAll(safe.appendChild(elem), "script");

              // Preserve script evaluation history
              if (contains) {
                setGlobalEval(tmp);
              }

              // Capture executables
              if (scripts) {
                j = 0;
                while ((elem = tmp[j++])) {
                  if (rscriptType.test(elem.type || "")) {
                    scripts.push(elem);
                  }
                }
              }
            }

            tmp = null;

            return safe;
          },

          cleanData: function (elems, /* internal */ acceptData) {
            var elem, type, id, data, i = 0,
              internalKey = jQuery.expando,
              cache = jQuery.cache,
              deleteExpando = jQuery.support.deleteExpando,
              special = jQuery.event.special;

            for (;
            (elem = elems[i]) != null; i++) {

              if (acceptData || jQuery.acceptData(elem)) {

                id = elem[internalKey];
                data = id && cache[id];

                if (data) {
                  if (data.events) {
                    for (type in data.events) {
                      if (special[type]) {
                        jQuery.event.remove(elem, type);

                        // This is a shortcut to avoid jQuery.event.remove's overhead
                      } else {
                        jQuery.removeEvent(elem, type, data.handle);
                      }
                    }
                  }

                  // Remove cache only if it was not already removed by jQuery.event.remove
                  if (cache[id]) {

                    delete cache[id];

                    // IE does not allow us to delete expando properties from nodes,
                    // nor does it have a removeAttribute function on Document nodes;
                    // we must handle all of these cases
                    if (deleteExpando) {
                      delete elem[internalKey];

                    } else if (typeof elem.removeAttribute !== core_strundefined) {
                      elem.removeAttribute(internalKey);

                    } else {
                      elem[internalKey] = null;
                    }

                    core_deletedIds.push(id);
                  }
                }
              }
            }
          }
        });
        var iframe, getStyles, curCSS, ralpha = /alpha\([^)]*\)/i,
          ropacity = /opacity\s*=\s*([^)]*)/,
          rposition = /^(top|right|bottom|left)$/,
          // swappable if display is none or starts with table except "table", "table-cell", or "table-caption"
          // see here for display values: https://developer.mozilla.org/en-US/docs/CSS/display
          rdisplayswap = /^(none|table(?!-c[ea]).+)/,
          rmargin = /^margin/,
          rnumsplit = new RegExp("^(" + core_pnum + ")(.*)$", "i"),
          rnumnonpx = new RegExp("^(" + core_pnum + ")(?!px)[a-z%]+$", "i"),
          rrelNum = new RegExp("^([+-])=(" + core_pnum + ")", "i"),
          elemdisplay = {
            BODY: "block"
          },

          cssShow = {
            position: "absolute",
            visibility: "hidden",
            display: "block"
          },
          cssNormalTransform = {
            letterSpacing: 0,
            fontWeight: 400
          },

          cssExpand = ["Top", "Right", "Bottom", "Left"],
          cssPrefixes = ["Webkit", "O", "Moz", "ms"];

        // return a css property mapped to a potentially vendor prefixed property
        function vendorPropName(style, name) {

          // shortcut for names that are not vendor prefixed
          if (name in style) {
            return name;
          }

          // check for vendor prefixed names
          var capName = name.charAt(0).toUpperCase() + name.slice(1),
            origName = name,
            i = cssPrefixes.length;

          while (i--) {
            name = cssPrefixes[i] + capName;
            if (name in style) {
              return name;
            }
          }

          return origName;
        }

        function isHidden(elem, el) {
          // isHidden might be called from jQuery#filter function;
          // in that case, element will be second argument
          elem = el || elem;
          return jQuery.css(elem, "display") === "none" || !jQuery.contains(elem.ownerDocument, elem);
        }

        function showHide(elements, show) {
          var display, elem, hidden, values = [],
            index = 0,
            length = elements.length;

          for (; index < length; index++) {
            elem = elements[index];
            if (!elem.style) {
              continue;
            }

            values[index] = jQuery._data(elem, "olddisplay");
            display = elem.style.display;
            if (show) {
              // Reset the inline display of this element to learn if it is
              // being hidden by cascaded rules or not
              if (!values[index] && display === "none") {
                elem.style.display = "";
              }

              // Set elements which have been overridden with display: none
              // in a stylesheet to whatever the default browser style is
              // for such an element
              if (elem.style.display === "" && isHidden(elem)) {
                values[index] = jQuery._data(elem, "olddisplay", css_defaultDisplay(elem.nodeName));
              }
            } else {

              if (!values[index]) {
                hidden = isHidden(elem);

                if (display && display !== "none" || !hidden) {
                  jQuery._data(elem, "olddisplay", hidden ? display : jQuery.css(elem, "display"));
                }
              }
            }
          }

          // Set the display of most of the elements in a second loop
          // to avoid the constant reflow
          for (index = 0; index < length; index++) {
            elem = elements[index];
            if (!elem.style) {
              continue;
            }
            if (!show || elem.style.display === "none" || elem.style.display === "") {
              elem.style.display = show ? values[index] || "" : "none";
            }
          }

          return elements;
        }

        jQuery.fn.extend({
          css: function (name, value) {
            return jQuery.access(this, function (elem, name, value) {
              var len, styles, map = {},
                i = 0;

              if (jQuery.isArray(name)) {
                styles = getStyles(elem);
                len = name.length;

                for (; i < len; i++) {
                  map[name[i]] = jQuery.css(elem, name[i], false, styles);
                }

                return map;
              }

              return value !== undefined ? jQuery.style(elem, name, value) : jQuery.css(elem, name);
            }, name, value, arguments.length > 1);
          },
          show: function () {
            return showHide(this, true);
          },
          hide: function () {
            return showHide(this);
          },
          toggle: function (state) {
            var bool = typeof state === "boolean";

            return this.each(function () {
              if (bool ? state : isHidden(this)) {
                jQuery(this).show();
              } else {
                jQuery(this).hide();
              }
            });
          }
        });

        jQuery.extend({
          // Add in style property hooks for overriding the default
          // behavior of getting and setting a style property
          cssHooks: {
            opacity: {
              get: function (elem, computed) {
                if (computed) {
                  // We should always get a number back from opacity
                  var ret = curCSS(elem, "opacity");
                  return ret === "" ? "1" : ret;
                }
              }
            }
          },

          // Exclude the following css properties to add px
          cssNumber: {
            "columnCount": true,
            "fillOpacity": true,
            "fontWeight": true,
            "lineHeight": true,
            "opacity": true,
            "orphans": true,
            "widows": true,
            "zIndex": true,
            "zoom": true
          },

          // Add in properties whose names you wish to fix before
          // setting or getting the value
          cssProps: {
            // normalize float css property
            "float": jQuery.support.cssFloat ? "cssFloat" : "styleFloat"
          },

          // Get and set the style property on a DOM Node
          style: function (elem, name, value, extra) {
            // Don't set styles on text and comment nodes
            if (!elem || elem.nodeType === 3 || elem.nodeType === 8 || !elem.style) {
              return;
            }

            // Make sure that we're working with the right name
            var ret, type, hooks, origName = jQuery.camelCase(name),
              style = elem.style;

            name = jQuery.cssProps[origName] || (jQuery.cssProps[origName] = vendorPropName(style, origName));

            // gets hook for the prefixed version
            // followed by the unprefixed version
            hooks = jQuery.cssHooks[name] || jQuery.cssHooks[origName];

            // Check if we're setting a value
            if (value !== undefined) {
              type = typeof value;

              // convert relative number strings (+= or -=) to relative numbers. #7345
              if (type === "string" && (ret = rrelNum.exec(value))) {
                value = (ret[1] + 1) * ret[2] + parseFloat(jQuery.css(elem, name));
                // Fixes bug #9237
                type = "number";
              }

              // Make sure that NaN and null values aren't set. See: #7116
              if (value == null || type === "number" && isNaN(value)) {
                return;
              }

              // If a number was passed in, add 'px' to the (except for certain CSS properties)
              if (type === "number" && !jQuery.cssNumber[origName]) {
                value += "px";
              }

              // Fixes #8908, it can be done more correctly by specifing setters in cssHooks,
              // but it would mean to define eight (for every problematic property) identical functions
              if (!jQuery.support.clearCloneStyle && value === "" && name.indexOf("background") === 0) {
                style[name] = "inherit";
              }

              // If a hook was provided, use that value, otherwise just set the specified value
              if (!hooks || !("set" in hooks) || (value = hooks.set(elem, value, extra)) !== undefined) {

                // Wrapped to prevent IE from throwing errors when 'invalid' values are provided
                // Fixes bug #5509
                try {
                  style[name] = value;
                } catch (e) {}
              }

            } else {
              // If a hook was provided get the non-computed value from there
              if (hooks && "get" in hooks && (ret = hooks.get(elem, false, extra)) !== undefined) {
                return ret;
              }

              // Otherwise just get the value from the style object
              return style[name];
            }
          },

          css: function (elem, name, extra, styles) {
            var num, val, hooks, origName = jQuery.camelCase(name);

            // Make sure that we're working with the right name
            name = jQuery.cssProps[origName] || (jQuery.cssProps[origName] = vendorPropName(elem.style, origName));

            // gets hook for the prefixed version
            // followed by the unprefixed version
            hooks = jQuery.cssHooks[name] || jQuery.cssHooks[origName];

            // If a hook was provided get the computed value from there
            if (hooks && "get" in hooks) {
              val = hooks.get(elem, true, extra);
            }

            // Otherwise, if a way to get the computed value exists, use that
            if (val === undefined) {
              val = curCSS(elem, name, styles);
            }

            //convert "normal" to computed value
            if (val === "normal" && name in cssNormalTransform) {
              val = cssNormalTransform[name];
            }

            // Return, converting to number if forced or a qualifier was provided and val looks numeric
            if (extra === "" || extra) {
              num = parseFloat(val);
              return extra === true || jQuery.isNumeric(num) ? num || 0 : val;
            }
            return val;
          },

          // A method for quickly swapping in/out CSS properties to get correct calculations
          swap: function (elem, options, callback, args) {
            var ret, name, old = {};

            // Remember the old values, and insert the new ones
            for (name in options) {
              old[name] = elem.style[name];
              elem.style[name] = options[name];
            }

            ret = callback.apply(elem, args || []);

            // Revert the old values
            for (name in options) {
              elem.style[name] = old[name];
            }

            return ret;
          }
        });

        // NOTE: we've included the "window" in window.getComputedStyle
        // because jsdom on node.js will break without it.
        if (window.getComputedStyle) {
          getStyles = function (elem) {
            return window.getComputedStyle(elem, null);
          };

          curCSS = function (elem, name, _computed) {
            var width, minWidth, maxWidth, computed = _computed || getStyles(elem),

              // getPropertyValue is only needed for .css('filter') in IE9, see #12537
              ret = computed ? computed.getPropertyValue(name) || computed[name] : undefined,
              style = elem.style;

            if (computed) {

              if (ret === "" && !jQuery.contains(elem.ownerDocument, elem)) {
                ret = jQuery.style(elem, name);
              }

              // A tribute to the "awesome hack by Dean Edwards"
              // Chrome < 17 and Safari 5.0 uses "computed value" instead of "used value" for margin-right
              // Safari 5.1.7 (at least) returns percentage for a larger set of values, but width seems to be reliably pixels
              // this is against the CSSOM draft spec: http://dev.w3.org/csswg/cssom/#resolved-values
              if (rnumnonpx.test(ret) && rmargin.test(name)) {

                // Remember the original values
                width = style.width;
                minWidth = style.minWidth;
                maxWidth = style.maxWidth;

                // Put in the new values to get a computed value out
                style.minWidth = style.maxWidth = style.width = ret;
                ret = computed.width;

                // Revert the changed values
                style.width = width;
                style.minWidth = minWidth;
                style.maxWidth = maxWidth;
              }
            }

            return ret;
          };
        } else if (document.documentElement.currentStyle) {
          getStyles = function (elem) {
            return elem.currentStyle;
          };

          curCSS = function (elem, name, _computed) {
            var left, rs, rsLeft, computed = _computed || getStyles(elem),
              ret = computed ? computed[name] : undefined,
              style = elem.style;

            // Avoid setting ret to empty string here
            // so we don't default to auto
            if (ret == null && style && style[name]) {
              ret = style[name];
            }

            // From the awesome hack by Dean Edwards
            // http://erik.eae.net/archives/2007/07/27/18.54.15/#comment-102291
            // If we're not dealing with a regular pixel number
            // but a number that has a weird ending, we need to convert it to pixels
            // but not position css attributes, as those are proportional to the parent element instead
            // and we can't measure the parent instead because it might trigger a "stacking dolls" problem
            if (rnumnonpx.test(ret) && !rposition.test(name)) {

              // Remember the original values
              left = style.left;
              rs = elem.runtimeStyle;
              rsLeft = rs && rs.left;

              // Put in the new values to get a computed value out
              if (rsLeft) {
                rs.left = elem.currentStyle.left;
              }
              style.left = name === "fontSize" ? "1em" : ret;
              ret = style.pixelLeft + "px";

              // Revert the changed values
              style.left = left;
              if (rsLeft) {
                rs.left = rsLeft;
              }
            }

            return ret === "" ? "auto" : ret;
          };
        }

        function setPositiveNumber(elem, value, subtract) {
          var matches = rnumsplit.exec(value);
          return matches ?
          // Guard against undefined "subtract", e.g., when used as in cssHooks
          Math.max(0, matches[1] - (subtract || 0)) + (matches[2] || "px") : value;
        }

        function augmentWidthOrHeight(elem, name, extra, isBorderBox, styles) {
          var i = extra === (isBorderBox ? "border" : "content") ?
          // If we already have the right measurement, avoid augmentation
          4 :
          // Otherwise initialize for horizontal or vertical properties
          name === "width" ? 1 : 0,

            val = 0;

          for (; i < 4; i += 2) {
            // both box models exclude margin, so add it if we want it
            if (extra === "margin") {
              val += jQuery.css(elem, extra + cssExpand[i], true, styles);
            }

            if (isBorderBox) {
              // border-box includes padding, so remove it if we want content
              if (extra === "content") {
                val -= jQuery.css(elem, "padding" + cssExpand[i], true, styles);
              }

              // at this point, extra isn't border nor margin, so remove border
              if (extra !== "margin") {
                val -= jQuery.css(elem, "border" + cssExpand[i] + "Width", true, styles);
              }
            } else {
              // at this point, extra isn't content, so add padding
              val += jQuery.css(elem, "padding" + cssExpand[i], true, styles);

              // at this point, extra isn't content nor padding, so add border
              if (extra !== "padding") {
                val += jQuery.css(elem, "border" + cssExpand[i] + "Width", true, styles);
              }
            }
          }

          return val;
        }

        function getWidthOrHeight(elem, name, extra) {

          // Start with offset property, which is equivalent to the border-box value
          var valueIsBorderBox = true,
            val = name === "width" ? elem.offsetWidth : elem.offsetHeight,
            styles = getStyles(elem),
            isBorderBox = jQuery.support.boxSizing && jQuery.css(elem, "boxSizing", false, styles) === "border-box";

          // some non-html elements return undefined for offsetWidth, so check for null/undefined
          // svg - https://bugzilla.mozilla.org/show_bug.cgi?id=649285
          // MathML - https://bugzilla.mozilla.org/show_bug.cgi?id=491668
          if (val <= 0 || val == null) {
            // Fall back to computed then uncomputed css if necessary
            val = curCSS(elem, name, styles);
            if (val < 0 || val == null) {
              val = elem.style[name];
            }

            // Computed unit is not pixels. Stop here and return.
            if (rnumnonpx.test(val)) {
              return val;
            }

            // we need the check for style in case a browser which returns unreliable values
            // for getComputedStyle silently falls back to the reliable elem.style
            valueIsBorderBox = isBorderBox && (jQuery.support.boxSizingReliable || val === elem.style[name]);

            // Normalize "", auto, and prepare for extra
            val = parseFloat(val) || 0;
          }

          // use the active box-sizing model to add/subtract irrelevant styles
          return (val + augmentWidthOrHeight(
          elem, name, extra || (isBorderBox ? "border" : "content"), valueIsBorderBox, styles)) + "px";
        }

        // Try to determine the default display value of an element
        function css_defaultDisplay(nodeName) {
          var doc = document,
            display = elemdisplay[nodeName];

          if (!display) {
            display = actualDisplay(nodeName, doc);

            // If the simple way fails, read from inside an iframe
            if (display === "none" || !display) {
              // Use the already-created iframe if possible
              iframe = (iframe || jQuery("<iframe frameborder='0' width='0' height='0'/>").css("cssText", "display:block !important")).appendTo(doc.documentElement);

              // Always write a new HTML skeleton so Webkit and Firefox don't choke on reuse
              doc = (iframe[0].contentWindow || iframe[0].contentDocument).document;
              doc.write("<!doctype html><html><body>");
              doc.close();

              display = actualDisplay(nodeName, doc);
              iframe.detach();
            }

            // Store the correct default display
            elemdisplay[nodeName] = display;
          }

          return display;
        }

        // Called ONLY from within css_defaultDisplay
        function actualDisplay(name, doc) {
          var elem = jQuery(doc.createElement(name)).appendTo(doc.body),
            display = jQuery.css(elem[0], "display");
          elem.remove();
          return display;
        }

        jQuery.each(["height", "width"], function (i, name) {
          jQuery.cssHooks[name] = {
            get: function (elem, computed, extra) {
              if (computed) {
                // certain elements can have dimension info if we invisibly show them
                // however, it must have a current display style that would benefit from this
                return elem.offsetWidth === 0 && rdisplayswap.test(jQuery.css(elem, "display")) ? jQuery.swap(elem, cssShow, function () {
                  return getWidthOrHeight(elem, name, extra);
                }) : getWidthOrHeight(elem, name, extra);
              }
            },

            set: function (elem, value, extra) {
              var styles = extra && getStyles(elem);
              return setPositiveNumber(elem, value, extra ? augmentWidthOrHeight(
              elem, name, extra, jQuery.support.boxSizing && jQuery.css(elem, "boxSizing", false, styles) === "border-box", styles) : 0);
            }
          };
        });

        if (!jQuery.support.opacity) {
          jQuery.cssHooks.opacity = {
            get: function (elem, computed) {
              // IE uses filters for opacity
              return ropacity.test((computed && elem.currentStyle ? elem.currentStyle.filter : elem.style.filter) || "") ? (0.01 * parseFloat(RegExp.$1)) + "" : computed ? "1" : "";
            },

            set: function (elem, value) {
              var style = elem.style,
                currentStyle = elem.currentStyle,
                opacity = jQuery.isNumeric(value) ? "alpha(opacity=" + value * 100 + ")" : "",
                filter = currentStyle && currentStyle.filter || style.filter || "";

              // IE has trouble with opacity if it does not have layout
              // Force it by setting the zoom level
              style.zoom = 1;

              // if setting opacity to 1, and no other filters exist - attempt to remove filter attribute #6652
              // if value === "", then remove inline opacity #12685
              if ((value >= 1 || value === "") && jQuery.trim(filter.replace(ralpha, "")) === "" && style.removeAttribute) {

                // Setting style.filter to null, "" & " " still leave "filter:" in the cssText
                // if "filter:" is present at all, clearType is disabled, we want to avoid this
                // style.removeAttribute is IE Only, but so apparently is this code path...
                style.removeAttribute("filter");

                // if there is no filter style applied in a css rule or unset inline opacity, we are done
                if (value === "" || currentStyle && !currentStyle.filter) {
                  return;
                }
              }

              // otherwise, set new filter values
              style.filter = ralpha.test(filter) ? filter.replace(ralpha, opacity) : filter + " " + opacity;
            }
          };
        }

        // These hooks cannot be added until DOM ready because the support test
        // for it is not run until after DOM ready
        jQuery(function () {
          if (!jQuery.support.reliableMarginRight) {
            jQuery.cssHooks.marginRight = {
              get: function (elem, computed) {
                if (computed) {
                  // WebKit Bug 13343 - getComputedStyle returns wrong value for margin-right
                  // Work around by temporarily setting element display to inline-block
                  return jQuery.swap(elem, {
                    "display": "inline-block"
                  }, curCSS, [elem, "marginRight"]);
                }
              }
            };
          }

          // Webkit bug: https://bugs.webkit.org/show_bug.cgi?id=29084
          // getComputedStyle returns percent when specified for top/left/bottom/right
          // rather than make the css module depend on the offset module, we just check for it here
          if (!jQuery.support.pixelPosition && jQuery.fn.position) {
            jQuery.each(["top", "left"], function (i, prop) {
              jQuery.cssHooks[prop] = {
                get: function (elem, computed) {
                  if (computed) {
                    computed = curCSS(elem, prop);
                    // if curCSS returns percentage, fallback to offset
                    return rnumnonpx.test(computed) ? jQuery(elem).position()[prop] + "px" : computed;
                  }
                }
              };
            });
          }

        });

        if (jQuery.expr && jQuery.expr.filters) {
          jQuery.expr.filters.hidden = function (elem) {
            // Support: Opera <= 12.12
            // Opera reports offsetWidths and offsetHeights less than zero on some elements
            return elem.offsetWidth <= 0 && elem.offsetHeight <= 0 || (!jQuery.support.reliableHiddenOffsets && ((elem.style && elem.style.display) || jQuery.css(elem, "display")) === "none");
          };

          jQuery.expr.filters.visible = function (elem) {
            return !jQuery.expr.filters.hidden(elem);
          };
        }

        // These hooks are used by animate to expand properties
        jQuery.each({
          margin: "",
          padding: "",
          border: "Width"
        }, function (prefix, suffix) {
          jQuery.cssHooks[prefix + suffix] = {
            expand: function (value) {
              var i = 0,
                expanded = {},

                // assumes a single number if not a string
                parts = typeof value === "string" ? value.split(" ") : [value];

              for (; i < 4; i++) {
                expanded[prefix + cssExpand[i] + suffix] = parts[i] || parts[i - 2] || parts[0];
              }

              return expanded;
            }
          };

          if (!rmargin.test(prefix)) {
            jQuery.cssHooks[prefix + suffix].set = setPositiveNumber;
          }
        });
        var r20 = /%20/g,
          rbracket = /\[\]$/,
          rCRLF = /\r?\n/g,
          rsubmitterTypes = /^(?:submit|button|image|reset|file)$/i,
          rsubmittable = /^(?:input|select|textarea|keygen)/i;

        jQuery.fn.extend({
          serialize: function () {
            return jQuery.param(this.serializeArray());
          },
          serializeArray: function () {
            return this.map(function () {
              // Can add propHook for "elements" to filter or add form elements
              var elements = jQuery.prop(this, "elements");
              return elements ? jQuery.makeArray(elements) : this;
            }).filter(function () {
              var type = this.type;
              // Use .is(":disabled") so that fieldset[disabled] works
              return this.name && !jQuery(this).is(":disabled") && rsubmittable.test(this.nodeName) && !rsubmitterTypes.test(type) && (this.checked || !manipulation_rcheckableType.test(type));
            }).map(function (i, elem) {
              var val = jQuery(this).val();

              return val == null ? null : jQuery.isArray(val) ? jQuery.map(val, function (val) {
                return {
                  name: elem.name,
                  value: val.replace(rCRLF, "\r\n")
                };
              }) : {
                name: elem.name,
                value: val.replace(rCRLF, "\r\n")
              };
            }).get();
          }
        });

        //Serialize an array of form elements or a set of
        //key/values into a query string
        jQuery.param = function (a, traditional) {
          var prefix, s = [],
            add = function (key, value) {
              // If value is a function, invoke it and return its value
              value = jQuery.isFunction(value) ? value() : (value == null ? "" : value);
              s[s.length] = encodeURIComponent(key) + "=" + encodeURIComponent(value);
            };

          // Set traditional to true for jQuery <= 1.3.2 behavior.
          if (traditional === undefined) {
            traditional = jQuery.ajaxSettings && jQuery.ajaxSettings.traditional;
          }

          // If an array was passed in, assume that it is an array of form elements.
          if (jQuery.isArray(a) || (a.jquery && !jQuery.isPlainObject(a))) {
            // Serialize the form elements
            jQuery.each(a, function () {
              add(this.name, this.value);
            });

          } else {
            // If traditional, encode the "old" way (the way 1.3.2 or older
            // did it), otherwise encode params recursively.
            for (prefix in a) {
              buildParams(prefix, a[prefix], traditional, add);
            }
          }

          // Return the resulting serialization
          return s.join("&").replace(r20, "+");
        };

        function buildParams(prefix, obj, traditional, add) {
          var name;

          if (jQuery.isArray(obj)) {
            // Serialize array item.
            jQuery.each(obj, function (i, v) {
              if (traditional || rbracket.test(prefix)) {
                // Treat each array item as a scalar.
                add(prefix, v);

              } else {
                // Item is non-scalar (array or object), encode its numeric index.
                buildParams(prefix + "[" + (typeof v === "object" ? i : "") + "]", v, traditional, add);
              }
            });

          } else if (!traditional && jQuery.type(obj) === "object") {
            // Serialize object item.
            for (name in obj) {
              buildParams(prefix + "[" + name + "]", obj[name], traditional, add);
            }

          } else {
            // Serialize scalar item.
            add(prefix, obj);
          }
        }
        jQuery.each(("blur focus focusin focusout load resize scroll unload click dblclick " + "mousedown mouseup mousemove mouseover mouseout mouseenter mouseleave " + "change select submit keydown keypress keyup error contextmenu").split(" "), function (i, name) {

          // Handle event binding
          jQuery.fn[name] = function (data, fn) {
            return arguments.length > 0 ? this.on(name, null, data, fn) : this.trigger(name);
          };
        });

        jQuery.fn.hover = function (fnOver, fnOut) {
          return this.mouseenter(fnOver).mouseleave(fnOut || fnOver);
        };
        var
        // Document location
        ajaxLocParts, ajaxLocation, ajax_nonce = jQuery.now(),

          ajax_rquery = /\?/,
          rhash = /#.*$/,
          rts = /([?&])_=[^&]*/,
          rheaders = /^(.*?):[ \t]*([^\r\n]*)\r?$/mg,
          // IE leaves an \r character at EOL
          // #7653, #8125, #8152: local protocol detection
          rlocalProtocol = /^(?:about|app|app-storage|.+-extension|file|res|widget):$/,
          rnoContent = /^(?:GET|HEAD)$/,
          rprotocol = /^\/\//,
          rurl = /^([\w.+-]+:)(?:\/\/([^\/?#:]*)(?::(\d+)|)|)/,

          // Keep a copy of the old load method
          _load = jQuery.fn.load,

          /* Prefilters
           * 1) They are useful to introduce custom dataTypes (see ajax/jsonp.js for an example)
           * 2) These are called:
           *    - BEFORE asking for a transport
           *    - AFTER param serialization (s.data is a string if s.processData is true)
           * 3) key is the dataType
           * 4) the catchall symbol "*" can be used
           * 5) execution will start with transport dataType and THEN continue down to "*" if needed
           */
          prefilters = {},

          /* Transports bindings
           * 1) key is the dataType
           * 2) the catchall symbol "*" can be used
           * 3) selection will start with transport dataType and THEN go to "*" if needed
           */
          transports = {},

          // Avoid comment-prolog char sequence (#10098); must appease lint and evade compression
          allTypes = "*/".concat("*");

        // #8138, IE may throw an exception when accessing
        // a field from window.location if document.domain has been set
        try {
          ajaxLocation = location.href;
        } catch (e) {
          // Use the href attribute of an A element
          // since IE will modify it given document.location
          ajaxLocation = document.createElement("a");
          ajaxLocation.href = "";
          ajaxLocation = ajaxLocation.href;
        }

        // Segment location into parts
        ajaxLocParts = rurl.exec(ajaxLocation.toLowerCase()) || [];

        // Base "constructor" for jQuery.ajaxPrefilter and jQuery.ajaxTransport
        function addToPrefiltersOrTransports(structure) {

          // dataTypeExpression is optional and defaults to "*"
          return function (dataTypeExpression, func) {

            if (typeof dataTypeExpression !== "string") {
              func = dataTypeExpression;
              dataTypeExpression = "*";
            }

            var dataType, i = 0,
              dataTypes = dataTypeExpression.toLowerCase().match(core_rnotwhite) || [];

            if (jQuery.isFunction(func)) {
              // For each dataType in the dataTypeExpression
              while ((dataType = dataTypes[i++])) {
                // Prepend if requested
                if (dataType[0] === "+") {
                  dataType = dataType.slice(1) || "*";
                  (structure[dataType] = structure[dataType] || []).unshift(func);

                  // Otherwise append
                } else {
                  (structure[dataType] = structure[dataType] || []).push(func);
                }
              }
            }
          };
        }

        // Base inspection function for prefilters and transports
        function inspectPrefiltersOrTransports(structure, options, originalOptions, jqXHR) {

          var inspected = {},
            seekingTransport = (structure === transports);

          function inspect(dataType) {
            var selected;
            inspected[dataType] = true;
            jQuery.each(structure[dataType] || [], function (_, prefilterOrFactory) {
              var dataTypeOrTransport = prefilterOrFactory(options, originalOptions, jqXHR);
              if (typeof dataTypeOrTransport === "string" && !seekingTransport && !inspected[dataTypeOrTransport]) {
                options.dataTypes.unshift(dataTypeOrTransport);
                inspect(dataTypeOrTransport);
                return false;
              } else if (seekingTransport) {
                return !(selected = dataTypeOrTransport);
              }
            });
            return selected;
          }

          return inspect(options.dataTypes[0]) || !inspected["*"] && inspect("*");
        }

        // A special extend for ajax options
        // that takes "flat" options (not to be deep extended)
        // Fixes #9887
        function ajaxExtend(target, src) {
          var deep, key, flatOptions = jQuery.ajaxSettings.flatOptions || {};

          for (key in src) {
            if (src[key] !== undefined) {
              (flatOptions[key] ? target : (deep || (deep = {})))[key] = src[key];
            }
          }
          if (deep) {
            jQuery.extend(true, target, deep);
          }

          return target;
        }

        jQuery.fn.load = function (url, params, callback) {
          if (typeof url !== "string" && _load) {
            return _load.apply(this, arguments);
          }

          var selector, response, type, self = this,
            off = url.indexOf(" ");

          if (off >= 0) {
            selector = url.slice(off, url.length);
            url = url.slice(0, off);
          }

          // If it's a function
          if (jQuery.isFunction(params)) {

            // We assume that it's the callback
            callback = params;
            params = undefined;

            // Otherwise, build a param string
          } else if (params && typeof params === "object") {
            type = "POST";
          }

          // If we have elements to modify, make the request
          if (self.length > 0) {
            jQuery.ajax({
              url: url,

              // if "type" variable is undefined, then "GET" method will be used
              type: type,
              dataType: "html",
              data: params
            }).done(function (responseText) {

              // Save response for use in complete callback
              response = arguments;

              self.html(selector ?

              // If a selector was specified, locate the right elements in a dummy div
              // Exclude scripts to avoid IE 'Permission Denied' errors
              jQuery("<div>").append(jQuery.parseHTML(responseText)).find(selector) :

              // Otherwise use the full result
              responseText);

            }).complete(callback &&
            function (jqXHR, status) {
              self.each(callback, response || [jqXHR.responseText, status, jqXHR]);
            });
          }

          return this;
        };

        // Attach a bunch of functions for handling common AJAX events
        jQuery.each(["ajaxStart", "ajaxStop", "ajaxComplete", "ajaxError", "ajaxSuccess", "ajaxSend"], function (i, type) {
          jQuery.fn[type] = function (fn) {
            return this.on(type, fn);
          };
        });

        jQuery.each(["get", "post"], function (i, method) {
          jQuery[method] = function (url, data, callback, type) {
            // shift arguments if data argument was omitted
            if (jQuery.isFunction(data)) {
              type = type || callback;
              callback = data;
              data = undefined;
            }

            return jQuery.ajax({
              url: url,
              type: method,
              dataType: type,
              data: data,
              success: callback
            });
          };
        });

        jQuery.extend({

          // Counter for holding the number of active queries
          active: 0,

          // Last-Modified header cache for next request
          lastModified: {},
          etag: {},

          ajaxSettings: {
            url: ajaxLocation,
            type: "GET",
            isLocal: rlocalProtocol.test(ajaxLocParts[1]),
            global: true,
            processData: true,
            async: true,
            contentType: "application/x-www-form-urlencoded; charset=UTF-8",
            /*
		timeout: 0,
		data: null,
		dataType: null,
		username: null,
		password: null,
		cache: null,
		throws: false,
		traditional: false,
		headers: {},
		*/

            accepts: {
              "*": allTypes,
              text: "text/plain",
              html: "text/html",
              xml: "application/xml, text/xml",
              json: "application/json, text/javascript"
            },

            contents: {
              xml: /xml/,
              html: /html/,
              json: /json/
            },

            responseFields: {
              xml: "responseXML",
              text: "responseText"
            },

            // Data converters
            // Keys separate source (or catchall "*") and destination types with a single space
            converters: {

              // Convert anything to text
              "* text": window.String,

              // Text to html (true = no transformation)
              "text html": true,

              // Evaluate text as a json expression
              "text json": jQuery.parseJSON,

              // Parse text as xml
              "text xml": jQuery.parseXML
            },

            // For options that shouldn't be deep extended:
            // you can add your own custom options here if
            // and when you create one that shouldn't be
            // deep extended (see ajaxExtend)
            flatOptions: {
              url: true,
              context: true
            }
          },

          // Creates a full fledged settings object into target
          // with both ajaxSettings and settings fields.
          // If target is omitted, writes into ajaxSettings.
          ajaxSetup: function (target, settings) {
            return settings ?

            // Building a settings object
            ajaxExtend(ajaxExtend(target, jQuery.ajaxSettings), settings) :

            // Extending ajaxSettings
            ajaxExtend(jQuery.ajaxSettings, target);
          },

          ajaxPrefilter: addToPrefiltersOrTransports(prefilters),
          ajaxTransport: addToPrefiltersOrTransports(transports),

          // Main method
          ajax: function (url, options) {

            // If url is an object, simulate pre-1.5 signature
            if (typeof url === "object") {
              options = url;
              url = undefined;
            }

            // Force options to be an object
            options = options || {};

            var // Cross-domain detection vars
            parts,
            // Loop variable
            i,
            // URL without anti-cache param
            cacheURL,
            // Response headers as string
            responseHeadersString,
            // timeout handle
            timeoutTimer,

            // To know if global events are to be dispatched
            fireGlobals,

            transport,
            // Response headers
            responseHeaders,
            // Create the final options object
            s = jQuery.ajaxSetup({}, options),
              // Callbacks context
              callbackContext = s.context || s,
              // Context for global events is callbackContext if it is a DOM node or jQuery collection
              globalEventContext = s.context && (callbackContext.nodeType || callbackContext.jquery) ? jQuery(callbackContext) : jQuery.event,
              // Deferreds
              deferred = jQuery.Deferred(),
              completeDeferred = jQuery.Callbacks("once memory"),
              // Status-dependent callbacks
              statusCode = s.statusCode || {},
              // Headers (they are sent all at once)
              requestHeaders = {},
              requestHeadersNames = {},
              // The jqXHR state
              state = 0,
              // Default abort message
              strAbort = "canceled",
              // Fake xhr
              jqXHR = {
                readyState: 0,

                // Builds headers hashtable if needed
                getResponseHeader: function (key) {
                  var match;
                  if (state === 2) {
                    if (!responseHeaders) {
                      responseHeaders = {};
                      while ((match = rheaders.exec(responseHeadersString))) {
                        responseHeaders[match[1].toLowerCase()] = match[2];
                      }
                    }
                    match = responseHeaders[key.toLowerCase()];
                  }
                  return match == null ? null : match;
                },

                // Raw string
                getAllResponseHeaders: function () {
                  return state === 2 ? responseHeadersString : null;
                },

                // Caches the header
                setRequestHeader: function (name, value) {
                  var lname = name.toLowerCase();
                  if (!state) {
                    name = requestHeadersNames[lname] = requestHeadersNames[lname] || name;
                    requestHeaders[name] = value;
                  }
                  return this;
                },

                // Overrides response content-type header
                overrideMimeType: function (type) {
                  if (!state) {
                    s.mimeType = type;
                  }
                  return this;
                },

                // Status-dependent callbacks
                statusCode: function (map) {
                  var code;
                  if (map) {
                    if (state < 2) {
                      for (code in map) {
                        // Lazy-add the new callback in a way that preserves old ones
                        statusCode[code] = [statusCode[code], map[code]];
                      }
                    } else {
                      // Execute the appropriate callbacks
                      jqXHR.always(map[jqXHR.status]);
                    }
                  }
                  return this;
                },

                // Cancel the request
                abort: function (statusText) {
                  var finalText = statusText || strAbort;
                  if (transport) {
                    transport.abort(finalText);
                  }
                  done(0, finalText);
                  return this;
                }
              };

            // Attach deferreds
            deferred.promise(jqXHR).complete = completeDeferred.add;
            jqXHR.success = jqXHR.done;
            jqXHR.error = jqXHR.fail;

            // Remove hash character (#7531: and string promotion)
            // Add protocol if not provided (#5866: IE7 issue with protocol-less urls)
            // Handle falsy url in the settings object (#10093: consistency with old signature)
            // We also use the url parameter if available
            s.url = ((url || s.url || ajaxLocation) + "").replace(rhash, "").replace(rprotocol, ajaxLocParts[1] + "//");

            // Alias method option to type as per ticket #12004
            s.type = options.method || options.type || s.method || s.type;

            // Extract dataTypes list
            s.dataTypes = jQuery.trim(s.dataType || "*").toLowerCase().match(core_rnotwhite) || [""];

            // A cross-domain request is in order when we have a protocol:host:port mismatch
            if (s.crossDomain == null) {
              parts = rurl.exec(s.url.toLowerCase());
              s.crossDomain = !! (parts && (parts[1] !== ajaxLocParts[1] || parts[2] !== ajaxLocParts[2] || (parts[3] || (parts[1] === "http:" ? 80 : 443)) != (ajaxLocParts[3] || (ajaxLocParts[1] === "http:" ? 80 : 443))));
            }

            // Convert data if not already a string
            if (s.data && s.processData && typeof s.data !== "string") {
              s.data = jQuery.param(s.data, s.traditional);
            }

            // Apply prefilters
            inspectPrefiltersOrTransports(prefilters, s, options, jqXHR);

            // If request was aborted inside a prefilter, stop there
            if (state === 2) {
              return jqXHR;
            }

            // We can fire global events as of now if asked to
            fireGlobals = s.global;

            // Watch for a new set of requests
            if (fireGlobals && jQuery.active++ === 0) {
              jQuery.event.trigger("ajaxStart");
            }

            // Uppercase the type
            s.type = s.type.toUpperCase();

            // Determine if request has content
            s.hasContent = !rnoContent.test(s.type);

            // Save the URL in case we're toying with the If-Modified-Since
            // and/or If-None-Match header later on
            cacheURL = s.url;

            // More options handling for requests with no content
            if (!s.hasContent) {

              // If data is available, append data to url
              if (s.data) {
                cacheURL = (s.url += (ajax_rquery.test(cacheURL) ? "&" : "?") + s.data);
                // #9682: remove data so that it's not used in an eventual retry
                delete s.data;
              }

              // Add anti-cache in url if needed
              if (s.cache === false) {
                s.url = rts.test(cacheURL) ?

                // If there is already a '_' parameter, set its value
                cacheURL.replace(rts, "$1_=" + ajax_nonce++) :

                // Otherwise add one to the end
                cacheURL + (ajax_rquery.test(cacheURL) ? "&" : "?") + "_=" + ajax_nonce++;
              }
            }

            // Set the If-Modified-Since and/or If-None-Match header, if in ifModified mode.
            if (s.ifModified) {
              if (jQuery.lastModified[cacheURL]) {
                jqXHR.setRequestHeader("If-Modified-Since", jQuery.lastModified[cacheURL]);
              }
              if (jQuery.etag[cacheURL]) {
                jqXHR.setRequestHeader("If-None-Match", jQuery.etag[cacheURL]);
              }
            }

            // Set the correct header, if data is being sent
            if (s.data && s.hasContent && s.contentType !== false || options.contentType) {
              jqXHR.setRequestHeader("Content-Type", s.contentType);
            }

            // Set the Accepts header for the server, depending on the dataType
            jqXHR.setRequestHeader("Accept", s.dataTypes[0] && s.accepts[s.dataTypes[0]] ? s.accepts[s.dataTypes[0]] + (s.dataTypes[0] !== "*" ? ", " + allTypes + "; q=0.01" : "") : s.accepts["*"]);

            // Check for headers option
            for (i in s.headers) {
              jqXHR.setRequestHeader(i, s.headers[i]);
            }

            // Allow custom headers/mimetypes and early abort
            if (s.beforeSend && (s.beforeSend.call(callbackContext, jqXHR, s) === false || state === 2)) {
              // Abort if not done already and return
              return jqXHR.abort();
            }

            // aborting is no longer a cancellation
            strAbort = "abort";

            // Install callbacks on deferreds
            for (i in {
              success: 1,
              error: 1,
              complete: 1
            }) {
              jqXHR[i](s[i]);
            }

            // Get transport
            transport = inspectPrefiltersOrTransports(transports, s, options, jqXHR);

            // If no transport, we auto-abort
            if (!transport) {
              done(-1, "No Transport");
            } else {
              jqXHR.readyState = 1;

              // Send global event
              if (fireGlobals) {
                globalEventContext.trigger("ajaxSend", [jqXHR, s]);
              }
              // Timeout
              if (s.async && s.timeout > 0) {
                timeoutTimer = setTimeout(function () {
                  jqXHR.abort("timeout");
                }, s.timeout);
              }

              try {
                state = 1;
                transport.send(requestHeaders, done);
              } catch (e) {
                // Propagate exception as error if not done
                if (state < 2) {
                  done(-1, e);
                  // Simply rethrow otherwise
                } else {
                  throw e;
                }
              }
            }

            // Callback for when everything is done
            function done(status, nativeStatusText, responses, headers) {
              var isSuccess, success, error, response, modified, statusText = nativeStatusText;

              // Called once
              if (state === 2) {
                return;
              }

              // State is "done" now
              state = 2;

              // Clear timeout if it exists
              if (timeoutTimer) {
                clearTimeout(timeoutTimer);
              }

              // Dereference transport for early garbage collection
              // (no matter how long the jqXHR object will be used)
              transport = undefined;

              // Cache response headers
              responseHeadersString = headers || "";

              // Set readyState
              jqXHR.readyState = status > 0 ? 4 : 0;

              // Get response data
              if (responses) {
                response = ajaxHandleResponses(s, jqXHR, responses);
              }

              // If successful, handle type chaining
              if (status >= 200 && status < 300 || status === 304) {

                // Set the If-Modified-Since and/or If-None-Match header, if in ifModified mode.
                if (s.ifModified) {
                  modified = jqXHR.getResponseHeader("Last-Modified");
                  if (modified) {
                    jQuery.lastModified[cacheURL] = modified;
                  }
                  modified = jqXHR.getResponseHeader("etag");
                  if (modified) {
                    jQuery.etag[cacheURL] = modified;
                  }
                }

                // if no content
                if (status === 204) {
                  isSuccess = true;
                  statusText = "nocontent";

                  // if not modified
                } else if (status === 304) {
                  isSuccess = true;
                  statusText = "notmodified";

                  // If we have data, let's convert it
                } else {
                  isSuccess = ajaxConvert(s, response);
                  statusText = isSuccess.state;
                  success = isSuccess.data;
                  error = isSuccess.error;
                  isSuccess = !error;
                }
              } else {
                // We extract error from statusText
                // then normalize statusText and status for non-aborts
                error = statusText;
                if (status || !statusText) {
                  statusText = "error";
                  if (status < 0) {
                    status = 0;
                  }
                }
              }

              // Set data for the fake xhr object
              jqXHR.status = status;
              jqXHR.statusText = (nativeStatusText || statusText) + "";

              // Success/Error
              if (isSuccess) {
                deferred.resolveWith(callbackContext, [success, statusText, jqXHR]);
              } else {
                deferred.rejectWith(callbackContext, [jqXHR, statusText, error]);
              }

              // Status-dependent callbacks
              jqXHR.statusCode(statusCode);
              statusCode = undefined;

              if (fireGlobals) {
                globalEventContext.trigger(isSuccess ? "ajaxSuccess" : "ajaxError", [jqXHR, s, isSuccess ? success : error]);
              }

              // Complete
              completeDeferred.fireWith(callbackContext, [jqXHR, statusText]);

              if (fireGlobals) {
                globalEventContext.trigger("ajaxComplete", [jqXHR, s]);
                // Handle the global AJAX counter
                if (!(--jQuery.active)) {
                  jQuery.event.trigger("ajaxStop");
                }
              }
            }

            return jqXHR;
          },

          getScript: function (url, callback) {
            return jQuery.get(url, undefined, callback, "script");
          },

          getJSON: function (url, data, callback) {
            return jQuery.get(url, data, callback, "json");
          }
        });

        /* Handles responses to an ajax request:
         * - sets all responseXXX fields accordingly
         * - finds the right dataType (mediates between content-type and expected dataType)
         * - returns the corresponding response
         */
        function ajaxHandleResponses(s, jqXHR, responses) {
          var firstDataType, ct, finalDataType, type, contents = s.contents,
            dataTypes = s.dataTypes,
            responseFields = s.responseFields;

          // Fill responseXXX fields
          for (type in responseFields) {
            if (type in responses) {
              jqXHR[responseFields[type]] = responses[type];
            }
          }

          // Remove auto dataType and get content-type in the process
          while (dataTypes[0] === "*") {
            dataTypes.shift();
            if (ct === undefined) {
              ct = s.mimeType || jqXHR.getResponseHeader("Content-Type");
            }
          }

          // Check if we're dealing with a known content-type
          if (ct) {
            for (type in contents) {
              if (contents[type] && contents[type].test(ct)) {
                dataTypes.unshift(type);
                break;
              }
            }
          }

          // Check to see if we have a response for the expected dataType
          if (dataTypes[0] in responses) {
            finalDataType = dataTypes[0];
          } else {
            // Try convertible dataTypes
            for (type in responses) {
              if (!dataTypes[0] || s.converters[type + " " + dataTypes[0]]) {
                finalDataType = type;
                break;
              }
              if (!firstDataType) {
                firstDataType = type;
              }
            }
            // Or just use first one
            finalDataType = finalDataType || firstDataType;
          }

          // If we found a dataType
          // We add the dataType to the list if needed
          // and return the corresponding response
          if (finalDataType) {
            if (finalDataType !== dataTypes[0]) {
              dataTypes.unshift(finalDataType);
            }
            return responses[finalDataType];
          }
        }

        // Chain conversions given the request and the original response
        function ajaxConvert(s, response) {
          var conv2, current, conv, tmp, converters = {},
            i = 0,
            // Work with a copy of dataTypes in case we need to modify it for conversion
            dataTypes = s.dataTypes.slice(),
            prev = dataTypes[0];

          // Apply the dataFilter if provided
          if (s.dataFilter) {
            response = s.dataFilter(response, s.dataType);
          }

          // Create converters map with lowercased keys
          if (dataTypes[1]) {
            for (conv in s.converters) {
              converters[conv.toLowerCase()] = s.converters[conv];
            }
          }

          // Convert to each sequential dataType, tolerating list modification
          for (;
          (current = dataTypes[++i]);) {

            // There's only work to do if current dataType is non-auto
            if (current !== "*") {

              // Convert response if prev dataType is non-auto and differs from current
              if (prev !== "*" && prev !== current) {

                // Seek a direct converter
                conv = converters[prev + " " + current] || converters["* " + current];

                // If none found, seek a pair
                if (!conv) {
                  for (conv2 in converters) {

                    // If conv2 outputs current
                    tmp = conv2.split(" ");
                    if (tmp[1] === current) {

                      // If prev can be converted to accepted input
                      conv = converters[prev + " " + tmp[0]] || converters["* " + tmp[0]];
                      if (conv) {
                        // Condense equivalence converters
                        if (conv === true) {
                          conv = converters[conv2];

                          // Otherwise, insert the intermediate dataType
                        } else if (converters[conv2] !== true) {
                          current = tmp[0];
                          dataTypes.splice(i--, 0, current);
                        }

                        break;
                      }
                    }
                  }
                }

                // Apply converter (if not an equivalence)
                if (conv !== true) {

                  // Unless errors are allowed to bubble, catch and return them
                  if (conv && s["throws"]) {
                    response = conv(response);
                  } else {
                    try {
                      response = conv(response);
                    } catch (e) {
                      return {
                        state: "parsererror",
                        error: conv ? e : "No conversion from " + prev + " to " + current
                      };
                    }
                  }
                }
              }

              // Update prev for next iteration
              prev = current;
            }
          }

          return {
            state: "success",
            data: response
          };
        }
        // Install script dataType
        jQuery.ajaxSetup({
          accepts: {
            script: "text/javascript, application/javascript, application/ecmascript, application/x-ecmascript"
          },
          contents: {
            script: /(?:java|ecma)script/
          },
          converters: {
            "text script": function (text) {
              jQuery.globalEval(text);
              return text;
            }
          }
        });

        // Handle cache's special case and global
        jQuery.ajaxPrefilter("script", function (s) {
          if (s.cache === undefined) {
            s.cache = false;
          }
          if (s.crossDomain) {
            s.type = "GET";
            s.global = false;
          }
        });

        // Bind script tag hack transport
        jQuery.ajaxTransport("script", function (s) {

          // This transport only deals with cross domain requests
          if (s.crossDomain) {

            var script, head = document.head || jQuery("head")[0] || document.documentElement;

            return {

              send: function (_, callback) {

                script = document.createElement("script");

                script.async = true;

                if (s.scriptCharset) {
                  script.charset = s.scriptCharset;
                }

                script.src = s.url;

                // Attach handlers for all browsers
                script.onload = script.onreadystatechange = function (_, isAbort) {

                  if (isAbort || !script.readyState || /loaded|complete/.test(script.readyState)) {

                    // Handle memory leak in IE
                    script.onload = script.onreadystatechange = null;

                    // Remove the script
                    if (script.parentNode) {
                      script.parentNode.removeChild(script);
                    }

                    // Dereference the script
                    script = null;

                    // Callback if not abort
                    if (!isAbort) {
                      callback(200, "success");
                    }
                  }
                };

                // Circumvent IE6 bugs with base elements (#2709 and #4378) by prepending
                // Use native DOM manipulation to avoid our domManip AJAX trickery
                head.insertBefore(script, head.firstChild);
              },

              abort: function () {
                if (script) {
                  script.onload(undefined, true);
                }
              }
            };
          }
        });
        var oldCallbacks = [],
          rjsonp = /(=)\?(?=&|$)|\?\?/;

        // Default jsonp settings
        jQuery.ajaxSetup({
          jsonp: "callback",
          jsonpCallback: function () {
            var callback = oldCallbacks.pop() || (jQuery.expando + "_" + (ajax_nonce++));
            this[callback] = true;
            return callback;
          }
        });

        // Detect, normalize options and install callbacks for jsonp requests
        jQuery.ajaxPrefilter("json jsonp", function (s, originalSettings, jqXHR) {

          var callbackName, overwritten, responseContainer, jsonProp = s.jsonp !== false && (rjsonp.test(s.url) ? "url" : typeof s.data === "string" && !(s.contentType || "").indexOf("application/x-www-form-urlencoded") && rjsonp.test(s.data) && "data");

          // Handle iff the expected data type is "jsonp" or we have a parameter to set
          if (jsonProp || s.dataTypes[0] === "jsonp") {

            // Get callback name, remembering preexisting value associated with it
            callbackName = s.jsonpCallback = jQuery.isFunction(s.jsonpCallback) ? s.jsonpCallback() : s.jsonpCallback;

            // Insert callback into url or form data
            if (jsonProp) {
              s[jsonProp] = s[jsonProp].replace(rjsonp, "$1" + callbackName);
            } else if (s.jsonp !== false) {
              s.url += (ajax_rquery.test(s.url) ? "&" : "?") + s.jsonp + "=" + callbackName;
            }

            // Use data converter to retrieve json after script execution
            s.converters["script json"] = function () {
              if (!responseContainer) {
                jQuery.error(callbackName + " was not called");
              }
              return responseContainer[0];
            };

            // force json dataType
            s.dataTypes[0] = "json";

            // Install callback
            overwritten = window[callbackName];
            window[callbackName] = function () {
              responseContainer = arguments;
            };

            // Clean-up function (fires after converters)
            jqXHR.always(function () {
              // Restore preexisting value
              window[callbackName] = overwritten;

              // Save back as free
              if (s[callbackName]) {
                // make sure that re-using the options doesn't screw things around
                s.jsonpCallback = originalSettings.jsonpCallback;

                // save the callback name for future use
                oldCallbacks.push(callbackName);
              }

              // Call if it was a function and we have a response
              if (responseContainer && jQuery.isFunction(overwritten)) {
                overwritten(responseContainer[0]);
              }

              responseContainer = overwritten = undefined;
            });

            // Delegate to script
            return "script";
          }
        });
        var xhrCallbacks, xhrSupported, xhrId = 0,
          // #5280: Internet Explorer will keep connections alive if we don't abort on unload
          xhrOnUnloadAbort = window.ActiveXObject &&
        function () {
          // Abort all pending requests
          var key;
          for (key in xhrCallbacks) {
            xhrCallbacks[key](undefined, true);
          }
        };

        // Functions to create xhrs
        function createStandardXHR() {
          try {
            return new window.XMLHttpRequest();
          } catch (e) {}
        }

        function createActiveXHR() {
          try {
            return new window.ActiveXObject("Microsoft.XMLHTTP");
          } catch (e) {}
        }

        // Create the request object
        // (This is still attached to ajaxSettings for backward compatibility)
        jQuery.ajaxSettings.xhr = window.ActiveXObject ?
        /* Microsoft failed to properly
         * implement the XMLHttpRequest in IE7 (can't request local files),
         * so we use the ActiveXObject when it is available
         * Additionally XMLHttpRequest can be disabled in IE7/IE8 so
         * we need a fallback.
         */
        function () {
          return !this.isLocal && createStandardXHR() || createActiveXHR();
        } :
        // For all other browsers, use the standard XMLHttpRequest object
        createStandardXHR;

        // Determine support properties
        xhrSupported = jQuery.ajaxSettings.xhr();
        jQuery.support.cors = !! xhrSupported && ("withCredentials" in xhrSupported);
        xhrSupported = jQuery.support.ajax = !! xhrSupported;

        // Create transport if the browser can provide an xhr
        if (xhrSupported) {

          jQuery.ajaxTransport(function (s) {
            // Cross domain only allowed if supported through XMLHttpRequest
            if (!s.crossDomain || jQuery.support.cors) {

              var callback;

              return {
                send: function (headers, complete) {

                  // Get a new xhr
                  var handle, i, xhr = s.xhr();

                  // Open the socket
                  // Passing null username, generates a login popup on Opera (#2865)
                  if (s.username) {
                    xhr.open(s.type, s.url, s.async, s.username, s.password);
                  } else {
                    xhr.open(s.type, s.url, s.async);
                  }

                  // Apply custom fields if provided
                  if (s.xhrFields) {
                    for (i in s.xhrFields) {
                      xhr[i] = s.xhrFields[i];
                    }
                  }

                  // Override mime type if needed
                  if (s.mimeType && xhr.overrideMimeType) {
                    xhr.overrideMimeType(s.mimeType);
                  }

                  // X-Requested-With header
                  // For cross-domain requests, seeing as conditions for a preflight are
                  // akin to a jigsaw puzzle, we simply never set it to be sure.
                  // (it can always be set on a per-request basis or even using ajaxSetup)
                  // For same-domain requests, won't change header if already provided.
                  if (!s.crossDomain && !headers["X-Requested-With"]) {
                    headers["X-Requested-With"] = "XMLHttpRequest";
                  }

                  // Need an extra try/catch for cross domain requests in Firefox 3
                  try {
                    for (i in headers) {
                      xhr.setRequestHeader(i, headers[i]);
                    }
                  } catch (err) {}

                  // Do send the request
                  // This may raise an exception which is actually
                  // handled in jQuery.ajax (so no try/catch here)
                  xhr.send((s.hasContent && s.data) || null);

                  // Listener
                  callback = function (_, isAbort) {
                    var status, responseHeaders, statusText, responses;

                    // Firefox throws exceptions when accessing properties
                    // of an xhr when a network error occurred
                    // http://helpful.knobs-dials.com/index.php/Component_returned_failure_code:_0x80040111_(NS_ERROR_NOT_AVAILABLE)
                    try {

                      // Was never called and is aborted or complete
                      if (callback && (isAbort || xhr.readyState === 4)) {

                        // Only called once
                        callback = undefined;

                        // Do not keep as active anymore
                        if (handle) {
                          xhr.onreadystatechange = jQuery.noop;
                          if (xhrOnUnloadAbort) {
                            delete xhrCallbacks[handle];
                          }
                        }

                        // If it's an abort
                        if (isAbort) {
                          // Abort it manually if needed
                          if (xhr.readyState !== 4) {
                            xhr.abort();
                          }
                        } else {
                          responses = {};
                          status = xhr.status;
                          responseHeaders = xhr.getAllResponseHeaders();

                          // When requesting binary data, IE6-9 will throw an exception
                          // on any attempt to access responseText (#11426)
                          if (typeof xhr.responseText === "string") {
                            responses.text = xhr.responseText;
                          }

                          // Firefox throws an exception when accessing
                          // statusText for faulty cross-domain requests
                          try {
                            statusText = xhr.statusText;
                          } catch (e) {
                            // We normalize with Webkit giving an empty statusText
                            statusText = "";
                          }

                          // Filter status for non standard behaviors
                          // If the request is local and we have data: assume a success
                          // (success with no data won't get notified, that's the best we
                          // can do given current implementations)
                          if (!status && s.isLocal && !s.crossDomain) {
                            status = responses.text ? 200 : 404;
                            // IE - #1450: sometimes returns 1223 when it should be 204
                          } else if (status === 1223) {
                            status = 204;
                          }
                        }
                      }
                    } catch (firefoxAccessException) {
                      if (!isAbort) {
                        complete(-1, firefoxAccessException);
                      }
                    }

                    // Call complete if needed
                    if (responses) {
                      complete(status, statusText, responses, responseHeaders);
                    }
                  };

                  if (!s.async) {
                    // if we're in sync mode we fire the callback
                    callback();
                  } else if (xhr.readyState === 4) {
                    // (IE6 & IE7) if it's in cache and has been
                    // retrieved directly we need to fire the callback
                    setTimeout(callback);
                  } else {
                    handle = ++xhrId;
                    if (xhrOnUnloadAbort) {
                      // Create the active xhrs callbacks list if needed
                      // and attach the unload handler
                      if (!xhrCallbacks) {
                        xhrCallbacks = {};
                        jQuery(window).unload(xhrOnUnloadAbort);
                      }
                      // Add to list of active xhrs callbacks
                      xhrCallbacks[handle] = callback;
                    }
                    xhr.onreadystatechange = callback;
                  }
                },

                abort: function () {
                  if (callback) {
                    callback(undefined, true);
                  }
                }
              };
            }
          });
        }
        var fxNow, timerId, rfxtypes = /^(?:toggle|show|hide)$/,
          rfxnum = new RegExp("^(?:([+-])=|)(" + core_pnum + ")([a-z%]*)$", "i"),
          rrun = /queueHooks$/,
          animationPrefilters = [defaultPrefilter],
          tweeners = {
            "*": [function (prop, value) {
              var end, unit, tween = this.createTween(prop, value),
                parts = rfxnum.exec(value),
                target = tween.cur(),
                start = +target || 0,
                scale = 1,
                maxIterations = 20;

              if (parts) {
                end = +parts[2];
                unit = parts[3] || (jQuery.cssNumber[prop] ? "" : "px");

                // We need to compute starting value
                if (unit !== "px" && start) {
                  // Iteratively approximate from a nonzero starting point
                  // Prefer the current property, because this process will be trivial if it uses the same units
                  // Fallback to end or a simple constant
                  start = jQuery.css(tween.elem, prop, true) || end || 1;

                  do {
                    // If previous iteration zeroed out, double until we get *something*
                    // Use a string for doubling factor so we don't accidentally see scale as unchanged below
                    scale = scale || ".5";

                    // Adjust and apply
                    start = start / scale;
                    jQuery.style(tween.elem, prop, start + unit);

                    // Update scale, tolerating zero or NaN from tween.cur()
                    // And breaking the loop if scale is unchanged or perfect, or if we've just had enough
                  } while (scale !== (scale = tween.cur() / target) && scale !== 1 && --maxIterations);
                }

                tween.unit = unit;
                tween.start = start;
                // If a +=/-= token was provided, we're doing a relative animation
                tween.end = parts[1] ? start + (parts[1] + 1) * end : end;
              }
              return tween;
            }]
          };

        // Animations created synchronously will run synchronously
        function createFxNow() {
          setTimeout(function () {
            fxNow = undefined;
          });
          return (fxNow = jQuery.now());
        }

        function createTweens(animation, props) {
          jQuery.each(props, function (prop, value) {
            var collection = (tweeners[prop] || []).concat(tweeners["*"]),
              index = 0,
              length = collection.length;
            for (; index < length; index++) {
              if (collection[index].call(animation, prop, value)) {

                // we're done with this property
                return;
              }
            }
          });
        }

        function Animation(elem, properties, options) {
          var result, stopped, index = 0,
            length = animationPrefilters.length,
            deferred = jQuery.Deferred().always(function () {
              // don't match elem in the :animated selector
              delete tick.elem;
            }),
            tick = function () {
              if (stopped) {
                return false;
              }
              var currentTime = fxNow || createFxNow(),
                remaining = Math.max(0, animation.startTime + animation.duration - currentTime),
                // archaic crash bug won't allow us to use 1 - ( 0.5 || 0 ) (#12497)
                temp = remaining / animation.duration || 0,
                percent = 1 - temp,
                index = 0,
                length = animation.tweens.length;

              for (; index < length; index++) {
                animation.tweens[index].run(percent);
              }

              deferred.notifyWith(elem, [animation, percent, remaining]);

              if (percent < 1 && length) {
                return remaining;
              } else {
                deferred.resolveWith(elem, [animation]);
                return false;
              }
            },
            animation = deferred.promise({
              elem: elem,
              props: jQuery.extend({}, properties),
              opts: jQuery.extend(true, {
                specialEasing: {}
              }, options),
              originalProperties: properties,
              originalOptions: options,
              startTime: fxNow || createFxNow(),
              duration: options.duration,
              tweens: [],
              createTween: function (prop, end) {
                var tween = jQuery.Tween(elem, animation.opts, prop, end, animation.opts.specialEasing[prop] || animation.opts.easing);
                animation.tweens.push(tween);
                return tween;
              },
              stop: function (gotoEnd) {
                var index = 0,
                  // if we are going to the end, we want to run all the tweens
                  // otherwise we skip this part
                  length = gotoEnd ? animation.tweens.length : 0;
                if (stopped) {
                  return this;
                }
                stopped = true;
                for (; index < length; index++) {
                  animation.tweens[index].run(1);
                }

                // resolve when we played the last frame
                // otherwise, reject
                if (gotoEnd) {
                  deferred.resolveWith(elem, [animation, gotoEnd]);
                } else {
                  deferred.rejectWith(elem, [animation, gotoEnd]);
                }
                return this;
              }
            }),
            props = animation.props;

          propFilter(props, animation.opts.specialEasing);

          for (; index < length; index++) {
            result = animationPrefilters[index].call(animation, elem, props, animation.opts);
            if (result) {
              return result;
            }
          }

          createTweens(animation, props);

          if (jQuery.isFunction(animation.opts.start)) {
            animation.opts.start.call(elem, animation);
          }

          jQuery.fx.timer(
          jQuery.extend(tick, {
            elem: elem,
            anim: animation,
            queue: animation.opts.queue
          }));

          // attach callbacks from options
          return animation.progress(animation.opts.progress).done(animation.opts.done, animation.opts.complete).fail(animation.opts.fail).always(animation.opts.always);
        }

        function propFilter(props, specialEasing) {
          var value, name, index, easing, hooks;

          // camelCase, specialEasing and expand cssHook pass
          for (index in props) {
            name = jQuery.camelCase(index);
            easing = specialEasing[name];
            value = props[index];
            if (jQuery.isArray(value)) {
              easing = value[1];
              value = props[index] = value[0];
            }

            if (index !== name) {
              props[name] = value;
              delete props[index];
            }

            hooks = jQuery.cssHooks[name];
            if (hooks && "expand" in hooks) {
              value = hooks.expand(value);
              delete props[name];

              // not quite $.extend, this wont overwrite keys already present.
              // also - reusing 'index' from above because we have the correct "name"
              for (index in value) {
                if (!(index in props)) {
                  props[index] = value[index];
                  specialEasing[index] = easing;
                }
              }
            } else {
              specialEasing[name] = easing;
            }
          }
        }

        jQuery.Animation = jQuery.extend(Animation, {

          tweener: function (props, callback) {
            if (jQuery.isFunction(props)) {
              callback = props;
              props = ["*"];
            } else {
              props = props.split(" ");
            }

            var prop, index = 0,
              length = props.length;

            for (; index < length; index++) {
              prop = props[index];
              tweeners[prop] = tweeners[prop] || [];
              tweeners[prop].unshift(callback);
            }
          },

          prefilter: function (callback, prepend) {
            if (prepend) {
              animationPrefilters.unshift(callback);
            } else {
              animationPrefilters.push(callback);
            }
          }
        });

        function defaultPrefilter(elem, props, opts) {
          /*jshint validthis:true */
          var prop, index, length, value, dataShow, toggle, tween, hooks, oldfire, anim = this,
            style = elem.style,
            orig = {},
            handled = [],
            hidden = elem.nodeType && isHidden(elem);

          // handle queue: false promises
          if (!opts.queue) {
            hooks = jQuery._queueHooks(elem, "fx");
            if (hooks.unqueued == null) {
              hooks.unqueued = 0;
              oldfire = hooks.empty.fire;
              hooks.empty.fire = function () {
                if (!hooks.unqueued) {
                  oldfire();
                }
              };
            }
            hooks.unqueued++;

            anim.always(function () {
              // doing this makes sure that the complete handler will be called
              // before this completes
              anim.always(function () {
                hooks.unqueued--;
                if (!jQuery.queue(elem, "fx").length) {
                  hooks.empty.fire();
                }
              });
            });
          }

          // height/width overflow pass
          if (elem.nodeType === 1 && ("height" in props || "width" in props)) {
            // Make sure that nothing sneaks out
            // Record all 3 overflow attributes because IE does not
            // change the overflow attribute when overflowX and
            // overflowY are set to the same value
            opts.overflow = [style.overflow, style.overflowX, style.overflowY];

            // Set display property to inline-block for height/width
            // animations on inline elements that are having width/height animated
            if (jQuery.css(elem, "display") === "inline" && jQuery.css(elem, "float") === "none") {

              // inline-level elements accept inline-block;
              // block-level elements need to be inline with layout
              if (!jQuery.support.inlineBlockNeedsLayout || css_defaultDisplay(elem.nodeName) === "inline") {
                style.display = "inline-block";

              } else {
                style.zoom = 1;
              }
            }
          }

          if (opts.overflow) {
            style.overflow = "hidden";
            if (!jQuery.support.shrinkWrapBlocks) {
              anim.always(function () {
                style.overflow = opts.overflow[0];
                style.overflowX = opts.overflow[1];
                style.overflowY = opts.overflow[2];
              });
            }
          }


          // show/hide pass
          for (index in props) {
            value = props[index];
            if (rfxtypes.exec(value)) {
              delete props[index];
              toggle = toggle || value === "toggle";
              if (value === (hidden ? "hide" : "show")) {
                continue;
              }
              handled.push(index);
            }
          }

          length = handled.length;
          if (length) {
            dataShow = jQuery._data(elem, "fxshow") || jQuery._data(elem, "fxshow", {});
            if ("hidden" in dataShow) {
              hidden = dataShow.hidden;
            }

            // store state if its toggle - enables .stop().toggle() to "reverse"
            if (toggle) {
              dataShow.hidden = !hidden;
            }
            if (hidden) {
              jQuery(elem).show();
            } else {
              anim.done(function () {
                jQuery(elem).hide();
              });
            }
            anim.done(function () {
              var prop;
              jQuery._removeData(elem, "fxshow");
              for (prop in orig) {
                jQuery.style(elem, prop, orig[prop]);
              }
            });
            for (index = 0; index < length; index++) {
              prop = handled[index];
              tween = anim.createTween(prop, hidden ? dataShow[prop] : 0);
              orig[prop] = dataShow[prop] || jQuery.style(elem, prop);

              if (!(prop in dataShow)) {
                dataShow[prop] = tween.start;
                if (hidden) {
                  tween.end = tween.start;
                  tween.start = prop === "width" || prop === "height" ? 1 : 0;
                }
              }
            }
          }
        }

        function Tween(elem, options, prop, end, easing) {
          return new Tween.prototype.init(elem, options, prop, end, easing);
        }
        jQuery.Tween = Tween;

        Tween.prototype = {
          constructor: Tween,
          init: function (elem, options, prop, end, easing, unit) {
            this.elem = elem;
            this.prop = prop;
            this.easing = easing || "swing";
            this.options = options;
            this.start = this.now = this.cur();
            this.end = end;
            this.unit = unit || (jQuery.cssNumber[prop] ? "" : "px");
          },
          cur: function () {
            var hooks = Tween.propHooks[this.prop];

            return hooks && hooks.get ? hooks.get(this) : Tween.propHooks._default.get(this);
          },
          run: function (percent) {
            var eased, hooks = Tween.propHooks[this.prop];

            if (this.options.duration) {
              this.pos = eased = jQuery.easing[this.easing](
              percent, this.options.duration * percent, 0, 1, this.options.duration);
            } else {
              this.pos = eased = percent;
            }
            this.now = (this.end - this.start) * eased + this.start;

            if (this.options.step) {
              this.options.step.call(this.elem, this.now, this);
            }

            if (hooks && hooks.set) {
              hooks.set(this);
            } else {
              Tween.propHooks._default.set(this);
            }
            return this;
          }
        };

        Tween.prototype.init.prototype = Tween.prototype;

        Tween.propHooks = {
          _default: {
            get: function (tween) {
              var result;

              if (tween.elem[tween.prop] != null && (!tween.elem.style || tween.elem.style[tween.prop] == null)) {
                return tween.elem[tween.prop];
              }

              // passing an empty string as a 3rd parameter to .css will automatically
              // attempt a parseFloat and fallback to a string if the parse fails
              // so, simple values such as "10px" are parsed to Float.
              // complex values such as "rotate(1rad)" are returned as is.
              result = jQuery.css(tween.elem, tween.prop, "");
              // Empty strings, null, undefined and "auto" are converted to 0.
              return !result || result === "auto" ? 0 : result;
            },
            set: function (tween) {
              // use step hook for back compat - use cssHook if its there - use .style if its
              // available and use plain properties where available
              if (jQuery.fx.step[tween.prop]) {
                jQuery.fx.step[tween.prop](tween);
              } else if (tween.elem.style && (tween.elem.style[jQuery.cssProps[tween.prop]] != null || jQuery.cssHooks[tween.prop])) {
                jQuery.style(tween.elem, tween.prop, tween.now + tween.unit);
              } else {
                tween.elem[tween.prop] = tween.now;
              }
            }
          }
        };

        // Remove in 2.0 - this supports IE8's panic based approach
        // to setting things on disconnected nodes
        Tween.propHooks.scrollTop = Tween.propHooks.scrollLeft = {
          set: function (tween) {
            if (tween.elem.nodeType && tween.elem.parentNode) {
              tween.elem[tween.prop] = tween.now;
            }
          }
        };

        jQuery.each(["toggle", "show", "hide"], function (i, name) {
          var cssFn = jQuery.fn[name];
          jQuery.fn[name] = function (speed, easing, callback) {
            return speed == null || typeof speed === "boolean" ? cssFn.apply(this, arguments) : this.animate(genFx(name, true), speed, easing, callback);
          };
        });

        jQuery.fn.extend({
          fadeTo: function (speed, to, easing, callback) {

            // show any hidden elements after setting opacity to 0
            return this.filter(isHidden).css("opacity", 0).show()

            // animate to the value specified
            .end().animate({
              opacity: to
            }, speed, easing, callback);
          },
          animate: function (prop, speed, easing, callback) {
            var empty = jQuery.isEmptyObject(prop),
              optall = jQuery.speed(speed, easing, callback),
              doAnimation = function () {
                // Operate on a copy of prop so per-property easing won't be lost
                var anim = Animation(this, jQuery.extend({}, prop), optall);
                doAnimation.finish = function () {
                  anim.stop(true);
                };
                // Empty animations, or finishing resolves immediately
                if (empty || jQuery._data(this, "finish")) {
                  anim.stop(true);
                }
              };
            doAnimation.finish = doAnimation;

            return empty || optall.queue === false ? this.each(doAnimation) : this.queue(optall.queue, doAnimation);
          },
          stop: function (type, clearQueue, gotoEnd) {
            var stopQueue = function (hooks) {
                var stop = hooks.stop;
                delete hooks.stop;
                stop(gotoEnd);
              };

            if (typeof type !== "string") {
              gotoEnd = clearQueue;
              clearQueue = type;
              type = undefined;
            }
            if (clearQueue && type !== false) {
              this.queue(type || "fx", []);
            }

            return this.each(function () {
              var dequeue = true,
                index = type != null && type + "queueHooks",
                timers = jQuery.timers,
                data = jQuery._data(this);

              if (index) {
                if (data[index] && data[index].stop) {
                  stopQueue(data[index]);
                }
              } else {
                for (index in data) {
                  if (data[index] && data[index].stop && rrun.test(index)) {
                    stopQueue(data[index]);
                  }
                }
              }

              for (index = timers.length; index--;) {
                if (timers[index].elem === this && (type == null || timers[index].queue === type)) {
                  timers[index].anim.stop(gotoEnd);
                  dequeue = false;
                  timers.splice(index, 1);
                }
              }

              // start the next in the queue if the last step wasn't forced
              // timers currently will call their complete callbacks, which will dequeue
              // but only if they were gotoEnd
              if (dequeue || !gotoEnd) {
                jQuery.dequeue(this, type);
              }
            });
          },
          finish: function (type) {
            if (type !== false) {
              type = type || "fx";
            }
            return this.each(function () {
              var index, data = jQuery._data(this),
                queue = data[type + "queue"],
                hooks = data[type + "queueHooks"],
                timers = jQuery.timers,
                length = queue ? queue.length : 0;

              // enable finishing flag on private data
              data.finish = true;

              // empty the queue first
              jQuery.queue(this, type, []);

              if (hooks && hooks.cur && hooks.cur.finish) {
                hooks.cur.finish.call(this);
              }

              // look for any active animations, and finish them
              for (index = timers.length; index--;) {
                if (timers[index].elem === this && timers[index].queue === type) {
                  timers[index].anim.stop(true);
                  timers.splice(index, 1);
                }
              }

              // look for any animations in the old queue and finish them
              for (index = 0; index < length; index++) {
                if (queue[index] && queue[index].finish) {
                  queue[index].finish.call(this);
                }
              }

              // turn off finishing flag
              delete data.finish;
            });
          }
        });

        // Generate parameters to create a standard animation
        function genFx(type, includeWidth) {
          var which, attrs = {
            height: type
          },
            i = 0;

          // if we include width, step value is 1 to do all cssExpand values,
          // if we don't include width, step value is 2 to skip over Left and Right
          includeWidth = includeWidth ? 1 : 0;
          for (; i < 4; i += 2 - includeWidth) {
            which = cssExpand[i];
            attrs["margin" + which] = attrs["padding" + which] = type;
          }

          if (includeWidth) {
            attrs.opacity = attrs.width = type;
          }

          return attrs;
        }

        // Generate shortcuts for custom animations
        jQuery.each({
          slideDown: genFx("show"),
          slideUp: genFx("hide"),
          slideToggle: genFx("toggle"),
          fadeIn: {
            opacity: "show"
          },
          fadeOut: {
            opacity: "hide"
          },
          fadeToggle: {
            opacity: "toggle"
          }
        }, function (name, props) {
          jQuery.fn[name] = function (speed, easing, callback) {
            return this.animate(props, speed, easing, callback);
          };
        });

        jQuery.speed = function (speed, easing, fn) {
          var opt = speed && typeof speed === "object" ? jQuery.extend({}, speed) : {
            complete: fn || !fn && easing || jQuery.isFunction(speed) && speed,
            duration: speed,
            easing: fn && easing || easing && !jQuery.isFunction(easing) && easing
          };

          opt.duration = jQuery.fx.off ? 0 : typeof opt.duration === "number" ? opt.duration : opt.duration in jQuery.fx.speeds ? jQuery.fx.speeds[opt.duration] : jQuery.fx.speeds._default;

          // normalize opt.queue - true/undefined/null -> "fx"
          if (opt.queue == null || opt.queue === true) {
            opt.queue = "fx";
          }

          // Queueing
          opt.old = opt.complete;

          opt.complete = function () {
            if (jQuery.isFunction(opt.old)) {
              opt.old.call(this);
            }

            if (opt.queue) {
              jQuery.dequeue(this, opt.queue);
            }
          };

          return opt;
        };

        jQuery.easing = {
          linear: function (p) {
            return p;
          },
          swing: function (p) {
            return 0.5 - Math.cos(p * Math.PI) / 2;
          }
        };

        jQuery.timers = [];
        jQuery.fx = Tween.prototype.init;
        jQuery.fx.tick = function () {
          var timer, timers = jQuery.timers,
            i = 0;

          fxNow = jQuery.now();

          for (; i < timers.length; i++) {
            timer = timers[i];
            // Checks the timer has not already been removed
            if (!timer() && timers[i] === timer) {
              timers.splice(i--, 1);
            }
          }

          if (!timers.length) {
            jQuery.fx.stop();
          }
          fxNow = undefined;
        };

        jQuery.fx.timer = function (timer) {
          if (timer() && jQuery.timers.push(timer)) {
            jQuery.fx.start();
          }
        };

        jQuery.fx.interval = 13;

        jQuery.fx.start = function () {
          if (!timerId) {
            timerId = setInterval(jQuery.fx.tick, jQuery.fx.interval);
          }
        };

        jQuery.fx.stop = function () {
          clearInterval(timerId);
          timerId = null;
        };

        jQuery.fx.speeds = {
          slow: 600,
          fast: 200,
          // Default speed
          _default: 400
        };

        // Back Compat <1.8 extension point
        jQuery.fx.step = {};

        if (jQuery.expr && jQuery.expr.filters) {
          jQuery.expr.filters.animated = function (elem) {
            return jQuery.grep(jQuery.timers, function (fn) {
              return elem === fn.elem;
            }).length;
          };
        }
        jQuery.fn.offset = function (options) {
          if (arguments.length) {
            return options === undefined ? this : this.each(function (i) {
              jQuery.offset.setOffset(this, options, i);
            });
          }

          var docElem, win, box = {
            top: 0,
            left: 0
          },
            elem = this[0],
            doc = elem && elem.ownerDocument;

          if (!doc) {
            return;
          }

          docElem = doc.documentElement;

          // Make sure it's not a disconnected DOM node
          if (!jQuery.contains(docElem, elem)) {
            return box;
          }

          // If we don't have gBCR, just use 0,0 rather than error
          // BlackBerry 5, iOS 3 (original iPhone)
          if (typeof elem.getBoundingClientRect !== core_strundefined) {
            box = elem.getBoundingClientRect();
          }
          win = getWindow(doc);
          return {
            top: box.top + (win.pageYOffset || docElem.scrollTop) - (docElem.clientTop || 0),
            left: box.left + (win.pageXOffset || docElem.scrollLeft) - (docElem.clientLeft || 0)
          };
        };

        jQuery.offset = {

          setOffset: function (elem, options, i) {
            var position = jQuery.css(elem, "position");

            // set position first, in-case top/left are set even on static elem
            if (position === "static") {
              elem.style.position = "relative";
            }

            var curElem = jQuery(elem),
              curOffset = curElem.offset(),
              curCSSTop = jQuery.css(elem, "top"),
              curCSSLeft = jQuery.css(elem, "left"),
              calculatePosition = (position === "absolute" || position === "fixed") && jQuery.inArray("auto", [curCSSTop, curCSSLeft]) > -1,
              props = {},
              curPosition = {},
              curTop, curLeft;

            // need to be able to calculate position if either top or left is auto and position is either absolute or fixed
            if (calculatePosition) {
              curPosition = curElem.position();
              curTop = curPosition.top;
              curLeft = curPosition.left;
            } else {
              curTop = parseFloat(curCSSTop) || 0;
              curLeft = parseFloat(curCSSLeft) || 0;
            }

            if (jQuery.isFunction(options)) {
              options = options.call(elem, i, curOffset);
            }

            if (options.top != null) {
              props.top = (options.top - curOffset.top) + curTop;
            }
            if (options.left != null) {
              props.left = (options.left - curOffset.left) + curLeft;
            }

            if ("using" in options) {
              options.using.call(elem, props);
            } else {
              curElem.css(props);
            }
          }
        };


        jQuery.fn.extend({

          position: function () {
            if (!this[0]) {
              return;
            }

            var offsetParent, offset, parentOffset = {
              top: 0,
              left: 0
            },
              elem = this[0];

            // fixed elements are offset from window (parentOffset = {top:0, left: 0}, because it is it's only offset parent
            if (jQuery.css(elem, "position") === "fixed") {
              // we assume that getBoundingClientRect is available when computed position is fixed
              offset = elem.getBoundingClientRect();
            } else {
              // Get *real* offsetParent
              offsetParent = this.offsetParent();

              // Get correct offsets
              offset = this.offset();
              if (!jQuery.nodeName(offsetParent[0], "html")) {
                parentOffset = offsetParent.offset();
              }

              // Add offsetParent borders
              parentOffset.top += jQuery.css(offsetParent[0], "borderTopWidth", true);
              parentOffset.left += jQuery.css(offsetParent[0], "borderLeftWidth", true);
            }

            // Subtract parent offsets and element margins
            // note: when an element has margin: auto the offsetLeft and marginLeft
            // are the same in Safari causing offset.left to incorrectly be 0
            return {
              top: offset.top - parentOffset.top - jQuery.css(elem, "marginTop", true),
              left: offset.left - parentOffset.left - jQuery.css(elem, "marginLeft", true)
            };
          },

          offsetParent: function () {
            return this.map(function () {
              var offsetParent = this.offsetParent || document.documentElement;
              while (offsetParent && (!jQuery.nodeName(offsetParent, "html") && jQuery.css(offsetParent, "position") === "static")) {
                offsetParent = offsetParent.offsetParent;
              }
              return offsetParent || document.documentElement;
            });
          }
        });


        // Create scrollLeft and scrollTop methods
        jQuery.each({
          scrollLeft: "pageXOffset",
          scrollTop: "pageYOffset"
        }, function (method, prop) {
          var top = /Y/.test(prop);

          jQuery.fn[method] = function (val) {
            return jQuery.access(this, function (elem, method, val) {
              var win = getWindow(elem);

              if (val === undefined) {
                return win ? (prop in win) ? win[prop] : win.document.documentElement[method] : elem[method];
              }

              if (win) {
                win.scrollTo(!top ? val : jQuery(win).scrollLeft(), top ? val : jQuery(win).scrollTop());

              } else {
                elem[method] = val;
              }
            }, method, val, arguments.length, null);
          };
        });

        function getWindow(elem) {
          return jQuery.isWindow(elem) ? elem : elem.nodeType === 9 ? elem.defaultView || elem.parentWindow : false;
        }
        // Create innerHeight, innerWidth, height, width, outerHeight and outerWidth methods
        jQuery.each({
          Height: "height",
          Width: "width"
        }, function (name, type) {
          jQuery.each({
            padding: "inner" + name,
            content: type,
            "": "outer" + name
          }, function (defaultExtra, funcName) {
            // margin is only for outerHeight, outerWidth
            jQuery.fn[funcName] = function (margin, value) {
              var chainable = arguments.length && (defaultExtra || typeof margin !== "boolean"),
                extra = defaultExtra || (margin === true || value === true ? "margin" : "border");

              return jQuery.access(this, function (elem, type, value) {
                var doc;

                if (jQuery.isWindow(elem)) {
                  // As of 5/8/2012 this will yield incorrect results for Mobile Safari, but there
                  // isn't a whole lot we can do. See pull request at this URL for discussion:
                  // https://github.com/jquery/jquery/pull/764
                  return elem.document.documentElement["client" + name];
                }

                // Get document width or height
                if (elem.nodeType === 9) {
                  doc = elem.documentElement;

                  // Either scroll[Width/Height] or offset[Width/Height] or client[Width/Height], whichever is greatest
                  // unfortunately, this causes bug #3838 in IE6/8 only, but there is currently no good, small way to fix it.
                  return Math.max(
                  elem.body["scroll" + name], doc["scroll" + name], elem.body["offset" + name], doc["offset" + name], doc["client" + name]);
                }

                return value === undefined ?
                // Get width or height on the element, requesting but not forcing parseFloat
                jQuery.css(elem, type, extra) :

                // Set width or height on the element
                jQuery.style(elem, type, value, extra);
              }, type, chainable ? margin : undefined, chainable, null);
            };
          });
        });
        // Limit scope pollution from any deprecated API
        // (function() {
        // })();
        // Expose jQuery to the global object
        window.jQuery = window.$ = jQuery;

        // Expose jQuery as an AMD module, but only for AMD loaders that
        // understand the issues with loading multiple versions of jQuery
        // in a page that all might call define(). The loader will indicate
        // they have special allowances for multiple jQuery versions by
        // specifying define.amd.jQuery = true. Register as a named module,
        // since jQuery can be concatenated with other files that may use define,
        // but not use a proper concatenation script that understands anonymous
        // AMD modules. A named AMD is safest and most robust way to register.
        // Lowercase jquery is used because AMD module names are derived from
        // file names, and jQuery is normally delivered in a lowercase file name.
        // Do this after creating the global so that if an AMD module wants to call
        // noConflict to hide this version of jQuery, it will work.
        if (typeof define === "function" && define.amd && define.amd.jQuery) {
          define("jquery", [], function () {
            return jQuery;
          });
        }

      })(window);
      /*! jQuery Migrate v1.1.1 | (c) 2005, 2013 jQuery Foundation, Inc. and other contributors | jquery.org/license */

      jQuery.migrateMute === void 0 && (jQuery.migrateMute = !0), function (e, t, n) {
        function r(n) {
          o[n] || (o[n] = !0, e.migrateWarnings.push(n), t.console && console.warn && !e.migrateMute && (console.warn("JQMIGRATE: " + n), e.migrateTrace && console.trace && console.trace()))
        }
        function a(t, a, o, i) {
          if (Object.defineProperty) try {
            return Object.defineProperty(t, a, {
              configurable: !0,
              enumerable: !0,
              get: function () {
                return r(i), o
              },
              set: function (e) {
                r(i), o = e
              }
            }), n
          } catch (s) {}
          e._definePropertyBroken = !0, t[a] = o
        }
        var o = {};
        e.migrateWarnings = [], !e.migrateMute && t.console && console.log && console.log("JQMIGRATE: Logging is active"), e.migrateTrace === n && (e.migrateTrace = !0), e.migrateReset = function () {
          o = {}, e.migrateWarnings.length = 0
        }, "BackCompat" === document.compatMode && r("jQuery is not compatible with Quirks Mode");
        var i = e("<input/>", {
          size: 1
        }).attr("size") && e.attrFn,
          s = e.attr,
          u = e.attrHooks.value && e.attrHooks.value.get ||
        function () {
          return null
        }, c = e.attrHooks.value && e.attrHooks.value.set ||
        function () {
          return n
        }, l = /^(?:input|button)$/i, d = /^[238]$/, p = /^(?:autofocus|autoplay|async|checked|controls|defer|disabled|hidden|loop|multiple|open|readonly|required|scoped|selected)$/i, f = /^(?:checked|selected)$/i;
        a(e, "attrFn", i || {}, "jQuery.attrFn is deprecated"), e.attr = function (t, a, o, u) {
          var c = a.toLowerCase(),
            g = t && t.nodeType;
          return u && (4 > s.length && r("jQuery.fn.attr( props, pass ) is deprecated"), t && !d.test(g) && (i ? a in i : e.isFunction(e.fn[a]))) ? e(t)[a](o) : ("type" === a && o !== n && l.test(t.nodeName) && t.parentNode && r("Can't change the 'type' of an input or button in IE 6/7/8"), !e.attrHooks[c] && p.test(c) && (e.attrHooks[c] = {
            get: function (t, r) {
              var a, o = e.prop(t, r);
              return o === !0 || "boolean" != typeof o && (a = t.getAttributeNode(r)) && a.nodeValue !== !1 ? r.toLowerCase() : n
            },
            set: function (t, n, r) {
              var a;
              return n === !1 ? e.removeAttr(t, r) : (a = e.propFix[r] || r, a in t && (t[a] = !0), t.setAttribute(r, r.toLowerCase())), r
            }
          }, f.test(c) && r("jQuery.fn.attr('" + c + "') may use property instead of attribute")), s.call(e, t, a, o))
        }, e.attrHooks.value = {
          get: function (e, t) {
            var n = (e.nodeName || "").toLowerCase();
            return "button" === n ? u.apply(this, arguments) : ("input" !== n && "option" !== n && r("jQuery.fn.attr('value') no longer gets properties"), t in e ? e.value : null)
          },
          set: function (e, t) {
            var a = (e.nodeName || "").toLowerCase();
            return "button" === a ? c.apply(this, arguments) : ("input" !== a && "option" !== a && r("jQuery.fn.attr('value', val) no longer sets properties"), e.value = t, n)
          }
        };
        var g, h, v = e.fn.init,
          m = e.parseJSON,
          y = /^(?:[^<]*(<[\w\W]+>)[^>]*|#([\w\-]*))$/;
        e.fn.init = function (t, n, a) {
          var o;
          return t && "string" == typeof t && !e.isPlainObject(n) && (o = y.exec(t)) && o[1] && ("<" !== t.charAt(0) && r("$(html) HTML strings must start with '<' character"), n && n.context && (n = n.context), e.parseHTML) ? v.call(this, e.parseHTML(e.trim(t), n, !0), n, a) : v.apply(this, arguments)
        }, e.fn.init.prototype = e.fn, e.parseJSON = function (e) {
          return e || null === e ? m.apply(this, arguments) : (r("jQuery.parseJSON requires a valid JSON string"), null)
        }, e.uaMatch = function (e) {
          e = e.toLowerCase();
          var t = /(chrome)[ \/]([\w.]+)/.exec(e) || /(webkit)[ \/]([\w.]+)/.exec(e) || /(opera)(?:.*version|)[ \/]([\w.]+)/.exec(e) || /(msie) ([\w.]+)/.exec(e) || 0 > e.indexOf("compatible") && /(mozilla)(?:.*? rv:([\w.]+)|)/.exec(e) || [];
          return {
            browser: t[1] || "",
            version: t[2] || "0"
          }
        }, e.browser || (g = e.uaMatch(navigator.userAgent), h = {}, g.browser && (h[g.browser] = !0, h.version = g.version), h.chrome ? h.webkit = !0 : h.webkit && (h.safari = !0), e.browser = h), a(e, "browser", e.browser, "jQuery.browser is deprecated"), e.sub = function () {
          function t(e, n) {
            return new t.fn.init(e, n)
          }
          e.extend(!0, t, this), t.superclass = this, t.fn = t.prototype = this(), t.fn.constructor = t, t.sub = this.sub, t.fn.init = function (r, a) {
            return a && a instanceof e && !(a instanceof t) && (a = t(a)), e.fn.init.call(this, r, a, n)
          }, t.fn.init.prototype = t.fn;
          var n = t(document);
          return r("jQuery.sub() is deprecated"), t
        }, e.ajaxSetup({
          converters: {
            "text json": e.parseJSON
          }
        });
        var b = e.fn.data;
        e.fn.data = function (t) {
          var a, o, i = this[0];
          return !i || "events" !== t || 1 !== arguments.length || (a = e.data(i, t), o = e._data(i, t), a !== n && a !== o || o === n) ? b.apply(this, arguments) : (r("Use of jQuery.fn.data('events') is deprecated"), o)
        };
        var j = /\/(java|ecma)script/i,
          w = e.fn.andSelf || e.fn.addBack;
        e.fn.andSelf = function () {
          return r("jQuery.fn.andSelf() replaced by jQuery.fn.addBack()"), w.apply(this, arguments)
        }, e.clean || (e.clean = function (t, a, o, i) {
          a = a || document, a = !a.nodeType && a[0] || a, a = a.ownerDocument || a, r("jQuery.clean() is deprecated");
          var s, u, c, l, d = [];
          if (e.merge(d, e.buildFragment(t, a).childNodes), o) for (c = function (e) {
            return !e.type || j.test(e.type) ? i ? i.push(e.parentNode ? e.parentNode.removeChild(e) : e) : o.appendChild(e) : n
          }, s = 0; null != (u = d[s]); s++) e.nodeName(u, "script") && c(u) || (o.appendChild(u), u.getElementsByTagName !== n && (l = e.grep(e.merge([], u.getElementsByTagName("script")), c), d.splice.apply(d, [s + 1, 0].concat(l)), s += l.length));
          return d
        });
        var Q = e.event.add,
          x = e.event.remove,
          k = e.event.trigger,
          N = e.fn.toggle,
          C = e.fn.live,
          S = e.fn.die,
          T = "ajaxStart|ajaxStop|ajaxSend|ajaxComplete|ajaxError|ajaxSuccess",
          M = RegExp("\\b(?:" + T + ")\\b"),
          H = /(?:^|\s)hover(\.\S+|)\b/,
          A = function (t) {
            return "string" != typeof t || e.event.special.hover ? t : (H.test(t) && r("'hover' pseudo-event is deprecated, use 'mouseenter mouseleave'"), t && t.replace(H, "mouseenter$1 mouseleave$1"))
          };
        e.event.props && "attrChange" !== e.event.props[0] && e.event.props.unshift("attrChange", "attrName", "relatedNode", "srcElement"), e.event.dispatch && a(e.event, "handle", e.event.dispatch, "jQuery.event.handle is undocumented and deprecated"), e.event.add = function (e, t, n, a, o) {
          e !== document && M.test(t) && r("AJAX events should be attached to document: " + t), Q.call(this, e, A(t || ""), n, a, o)
        }, e.event.remove = function (e, t, n, r, a) {
          x.call(this, e, A(t) || "", n, r, a)
        }, e.fn.error = function () {
          var e = Array.prototype.slice.call(arguments, 0);
          return r("jQuery.fn.error() is deprecated"), e.splice(0, 0, "error"), arguments.length ? this.bind.apply(this, e) : (this.triggerHandler.apply(this, e), this)
        }, e.fn.toggle = function (t, n) {
          if (!e.isFunction(t) || !e.isFunction(n)) return N.apply(this, arguments);
          r("jQuery.fn.toggle(handler, handler...) is deprecated");
          var a = arguments,
            o = t.guid || e.guid++,
            i = 0,
            s = function (n) {
              var r = (e._data(this, "lastToggle" + t.guid) || 0) % i;
              return e._data(this, "lastToggle" + t.guid, r + 1), n.preventDefault(), a[r].apply(this, arguments) || !1
            };
          for (s.guid = o; a.length > i;) a[i++].guid = o;
          return this.click(s)
        }, e.fn.live = function (t, n, a) {
          return r("jQuery.fn.live() is deprecated"), C ? C.apply(this, arguments) : (e(this.context).on(t, this.selector, n, a), this)
        }, e.fn.die = function (t, n) {
          return r("jQuery.fn.die() is deprecated"), S ? S.apply(this, arguments) : (e(this.context).off(t, this.selector || "**", n), this)
        }, e.event.trigger = function (e, t, n, a) {
          return n || M.test(e) || r("Global events are undocumented and deprecated"), k.call(this, e, t, n || document, a)
        }, e.each(T.split("|"), function (t, n) {
          e.event.special[n] = {
            setup: function () {
              var t = this;
              return t !== document && (e.event.add(document, n + "." + e.guid, function () {
                e.event.trigger(n, null, t, !0)
              }), e._data(this, n, e.guid++)), !1
            },
            teardown: function () {
              return this !== document && e.event.remove(document, n + "." + e._data(this, n)), !1
            }
          }
        })
      }(jQuery, window);
      //@ sourceMappingURL=dist/jquery-migrate.min.map
      ;
      (function ($, undefined) {

        /**
         * Unobtrusive scripting adapter for jQuery
         * https://github.com/rails/jquery-ujs
         *
         * Requires jQuery 1.7.0 or later.
         *
         * Released under the MIT license
         *
         */

        // Cut down on the number if issues from people inadvertently including jquery_ujs twice
        // by detecting and raising an error when it happens.
        var alreadyInitialized = function () {
            var events = $._data(document, 'events');
            return events && events.click && $.grep(events.click, function (e) {
              return e.namespace === 'rails';
            }).length;
          }

        if (alreadyInitialized()) {
          $.error('jquery-ujs has already been loaded!');
        }

        // Shorthand to make it a little easier to call public rails functions from within rails.js
        var rails;

        $.rails = rails = {
          // Link elements bound by jquery-ujs
          linkClickSelector: 'a[data-confirm], a[data-method], a[data-remote], a[data-disable-with]',

          // Select elements bound by jquery-ujs
          inputChangeSelector: 'select[data-remote], input[data-remote], textarea[data-remote]',

          // Form elements bound by jquery-ujs
          formSubmitSelector: 'form',

          // Form input elements bound by jquery-ujs
          formInputClickSelector: 'form input[type=submit], form input[type=image], form button[type=submit], form button:not([type])',

          // Form input elements disabled during form submission
          disableSelector: 'input[data-disable-with], button[data-disable-with], textarea[data-disable-with]',

          // Form input elements re-enabled after form submission
          enableSelector: 'input[data-disable-with]:disabled, button[data-disable-with]:disabled, textarea[data-disable-with]:disabled',

          // Form required input elements
          requiredInputSelector: 'input[name][required]:not([disabled]),textarea[name][required]:not([disabled])',

          // Form file input elements
          fileInputSelector: 'input[type=file]',

          // Link onClick disable selector with possible reenable after remote submission
          linkDisableSelector: 'a[data-disable-with]',

          // Make sure that every Ajax request sends the CSRF token
          CSRFProtection: function (xhr) {
            var token = $('meta[name="csrf-token"]').attr('content');
            if (token) xhr.setRequestHeader('X-CSRF-Token', token);
          },

          // Triggers an event on an element and returns false if the event result is false
          fire: function (obj, name, data) {
            var event = $.Event(name);
            obj.trigger(event, data);
            return event.result !== false;
          },

          // Default confirm dialog, may be overridden with custom confirm dialog in $.rails.confirm
          confirm: function (message) {
            return confirm(message);
          },

          // Default ajax function, may be overridden with custom function in $.rails.ajax
          ajax: function (options) {
            return $.ajax(options);
          },

          // Default way to get an element's href. May be overridden at $.rails.href.
          href: function (element) {
            return element.attr('href');
          },

          // Submits "remote" forms and links with ajax
          handleRemote: function (element) {
            var method, url, data, elCrossDomain, crossDomain, withCredentials, dataType, options;

            if (rails.fire(element, 'ajax:before')) {
              elCrossDomain = element.data('cross-domain');
              crossDomain = elCrossDomain === undefined ? null : elCrossDomain;
              withCredentials = element.data('with-credentials') || null;
              dataType = element.data('type') || ($.ajaxSettings && $.ajaxSettings.dataType);

              if (element.is('form')) {
                method = element.attr('method');
                url = element.attr('action');
                data = element.serializeArray();
                // memoized value from clicked submit button
                var button = element.data('ujs:submit-button');
                if (button) {
                  data.push(button);
                  element.data('ujs:submit-button', null);
                }
              } else if (element.is(rails.inputChangeSelector)) {
                method = element.data('method');
                url = element.data('url');
                data = element.serialize();
                if (element.data('params')) data = data + "&" + element.data('params');
              } else {
                method = element.data('method');
                url = rails.href(element);
                data = element.data('params') || null;
              }

              options = {
                type: method || 'GET',
                data: data,
                dataType: dataType,
                // stopping the "ajax:beforeSend" event will cancel the ajax request
                beforeSend: function (xhr, settings) {
                  if (settings.dataType === undefined) {
                    xhr.setRequestHeader('accept', '*/*;q=0.5, ' + settings.accepts.script);
                  }
                  return rails.fire(element, 'ajax:beforeSend', [xhr, settings]);
                },
                success: function (data, status, xhr) {
                  element.trigger('ajax:success', [data, status, xhr]);
                },
                complete: function (xhr, status) {
                  element.trigger('ajax:complete', [xhr, status]);
                },
                error: function (xhr, status, error) {
                  element.trigger('ajax:error', [xhr, status, error]);
                },
                crossDomain: crossDomain
              };

              // There is no withCredentials for IE6-8 when
              // "Enable native XMLHTTP support" is disabled
              if (withCredentials) {
                options.xhrFields = {
                  withCredentials: withCredentials
                };
              }

              // Only pass url to `ajax` options if not blank
              if (url) {
                options.url = url;
              }

              var jqxhr = rails.ajax(options);
              element.trigger('ajax:send', jqxhr);
              return jqxhr;
            } else {
              return false;
            }
          },

          // Handles "data-method" on links such as:
          // <a href="/users/5" data-method="delete" rel="nofollow" data-confirm="Are you sure?">Delete</a>
          handleMethod: function (link) {
            var href = rails.href(link),
              method = link.data('method'),
              target = link.attr('target'),
              csrf_token = $('meta[name=csrf-token]').attr('content'),
              csrf_param = $('meta[name=csrf-param]').attr('content'),
              form = $('<form method="post" action="' + href + '"></form>'),
              metadata_input = '<input name="_method" value="' + method + '" type="hidden" />';

            if (csrf_param !== undefined && csrf_token !== undefined) {
              metadata_input += '<input name="' + csrf_param + '" value="' + csrf_token + '" type="hidden" />';
            }

            if (target) {
              form.attr('target', target);
            }

            form.hide().append(metadata_input).appendTo('body');
            form.submit();
          },

          /* Disables form elements:
      - Caches element value in 'ujs:enable-with' data store
      - Replaces element text with value of 'data-disable-with' attribute
      - Sets disabled property to true
    */
          disableFormElements: function (form) {
            form.find(rails.disableSelector).each(function () {
              var element = $(this),
                method = element.is('button') ? 'html' : 'val';
              element.data('ujs:enable-with', element[method]());
              element[method](element.data('disable-with'));
              element.prop('disabled', true);
            });
          },

          /* Re-enables disabled form elements:
      - Replaces element text with cached value from 'ujs:enable-with' data store (created in `disableFormElements`)
      - Sets disabled property to false
    */
          enableFormElements: function (form) {
            form.find(rails.enableSelector).each(function () {
              var element = $(this),
                method = element.is('button') ? 'html' : 'val';
              if (element.data('ujs:enable-with')) element[method](element.data('ujs:enable-with'));
              element.prop('disabled', false);
            });
          },

          /* For 'data-confirm' attribute:
      - Fires `confirm` event
      - Shows the confirmation dialog
      - Fires the `confirm:complete` event

      Returns `true` if no function stops the chain and user chose yes; `false` otherwise.
      Attaching a handler to the element's `confirm` event that returns a `falsy` value cancels the confirmation dialog.
      Attaching a handler to the element's `confirm:complete` event that returns a `falsy` value makes this function
      return false. The `confirm:complete` event is fired whether or not the user answered true or false to the dialog.
   */
          allowAction: function (element) {
            var message = element.data('confirm'),
              answer = false,
              callback;
            if (!message) {
              return true;
            }

            if (rails.fire(element, 'confirm')) {
              answer = rails.confirm(message);
              callback = rails.fire(element, 'confirm:complete', [answer]);
            }
            return answer && callback;
          },

          // Helper function which checks for blank inputs in a form that match the specified CSS selector
          blankInputs: function (form, specifiedSelector, nonBlank) {
            var inputs = $(),
              input, valueToCheck, selector = specifiedSelector || 'input,textarea',
              allInputs = form.find(selector);

            allInputs.each(function () {
              input = $(this);
              valueToCheck = input.is('input[type=checkbox],input[type=radio]') ? input.is(':checked') : input.val();
              // If nonBlank and valueToCheck are both truthy, or nonBlank and valueToCheck are both falsey
              if (!valueToCheck === !nonBlank) {

                // Don't count unchecked required radio if other radio with same name is checked
                if (input.is('input[type=radio]') && allInputs.filter('input[type=radio]:checked[name="' + input.attr('name') + '"]').length) {
                  return true; // Skip to next input
                }

                inputs = inputs.add(input);
              }
            });
            return inputs.length ? inputs : false;
          },

          // Helper function which checks for non-blank inputs in a form that match the specified CSS selector
          nonBlankInputs: function (form, specifiedSelector) {
            return rails.blankInputs(form, specifiedSelector, true); // true specifies nonBlank
          },

          // Helper function, needed to provide consistent behavior in IE
          stopEverything: function (e) {
            $(e.target).trigger('ujs:everythingStopped');
            e.stopImmediatePropagation();
            return false;
          },

          // find all the submit events directly bound to the form and
          // manually invoke them. If anyone returns false then stop the loop
          callFormSubmitBindings: function (form, event) {
            var events = form.data('events'),
              continuePropagation = true;
            if (events !== undefined && events['submit'] !== undefined) {
              $.each(events['submit'], function (i, obj) {
                if (typeof obj.handler === 'function') return continuePropagation = obj.handler(event);
              });
            }
            return continuePropagation;
          },

          //  replace element's html with the 'data-disable-with' after storing original html
          //  and prevent clicking on it
          disableElement: function (element) {
            element.data('ujs:enable-with', element.html()); // store enabled state
            element.html(element.data('disable-with')); // set to disabled state
            element.bind('click.railsDisable', function (e) { // prevent further clicking
              return rails.stopEverything(e);
            });
          },

          // restore element to its original state which was disabled by 'disableElement' above
          enableElement: function (element) {
            if (element.data('ujs:enable-with') !== undefined) {
              element.html(element.data('ujs:enable-with')); // set to old enabled state
              // this should be element.removeData('ujs:enable-with')
              // but, there is currently a bug in jquery which makes hyphenated data attributes not get removed
              element.data('ujs:enable-with', false); // clean up cache
            }
            element.unbind('click.railsDisable'); // enable element
          }

        };

        if (rails.fire($(document), 'rails:attachBindings')) {

          $.ajaxPrefilter(function (options, originalOptions, xhr) {
            if (!options.crossDomain) {
              rails.CSRFProtection(xhr);
            }
          });

          $(document).delegate(rails.linkDisableSelector, 'ajax:complete', function () {
            rails.enableElement($(this));
          });

          $(document).delegate(rails.linkClickSelector, 'click.rails', function (e) {
            var link = $(this),
              method = link.data('method'),
              data = link.data('params');
            if (!rails.allowAction(link)) return rails.stopEverything(e);

            if (link.is(rails.linkDisableSelector)) rails.disableElement(link);

            if (link.data('remote') !== undefined) {
              if ((e.metaKey || e.ctrlKey) && (!method || method === 'GET') && !data) {
                return true;
              }

              var handleRemote = rails.handleRemote(link);
              // response from rails.handleRemote() will either be false or a deferred object promise.
              if (handleRemote === false) {
                rails.enableElement(link);
              } else {
                handleRemote.error(function () {
                  rails.enableElement(link);
                });
              }
              return false;

            } else if (link.data('method')) {
              rails.handleMethod(link);
              return false;
            }
          });

          $(document).delegate(rails.inputChangeSelector, 'change.rails', function (e) {
            var link = $(this);
            if (!rails.allowAction(link)) return rails.stopEverything(e);

            rails.handleRemote(link);
            return false;
          });

          $(document).delegate(rails.formSubmitSelector, 'submit.rails', function (e) {
            var form = $(this),
              remote = form.data('remote') !== undefined,
              blankRequiredInputs = rails.blankInputs(form, rails.requiredInputSelector),
              nonBlankFileInputs = rails.nonBlankInputs(form, rails.fileInputSelector);

            if (!rails.allowAction(form)) return rails.stopEverything(e);

            // skip other logic when required values are missing or file upload is present
            if (blankRequiredInputs && form.attr("novalidate") == undefined && rails.fire(form, 'ajax:aborted:required', [blankRequiredInputs])) {
              return rails.stopEverything(e);
            }

            if (remote) {
              if (nonBlankFileInputs) {
                // slight timeout so that the submit button gets properly serialized
                // (make it easy for event handler to serialize form without disabled values)
                setTimeout(function () {
                  rails.disableFormElements(form);
                }, 13);
                var aborted = rails.fire(form, 'ajax:aborted:file', [nonBlankFileInputs]);

                // re-enable form elements if event bindings return false (canceling normal form submission)
                if (!aborted) {
                  setTimeout(function () {
                    rails.enableFormElements(form);
                  }, 13);
                }

                return aborted;
              }

              // If browser does not support submit bubbling, then this live-binding will be called before direct
              // bindings. Therefore, we should directly call any direct bindings before remotely submitting form.
              if (!$.support.submitBubbles && $().jquery < '1.7' && rails.callFormSubmitBindings(form, e) === false) return rails.stopEverything(e);

              rails.handleRemote(form);
              return false;

            } else {
              // slight timeout so that the submit button gets properly serialized
              setTimeout(function () {
                rails.disableFormElements(form);
              }, 13);
            }
          });

          $(document).delegate(rails.formInputClickSelector, 'click.rails', function (event) {
            var button = $(this);

            if (!rails.allowAction(button)) return rails.stopEverything(event);

            // register the pressed submit button
            var name = button.attr('name'),
              data = name ? {
                name: name,
                value: button.val()
              } : null;

            button.closest('form').data('ujs:submit-button', data);
          });

          $(document).delegate(rails.formSubmitSelector, 'ajax:beforeSend.rails', function (event) {
            if (this == event.target) rails.disableFormElements($(this));
          });

          $(document).delegate(rails.formSubmitSelector, 'ajax:complete.rails', function (event) {
            if (this == event.target) rails.enableFormElements($(this));
          });

          $(function () {
            // making sure that all forms have actual up-to-date token(cached forms contain old one)
            var csrf_token = $('meta[name=csrf-token]').attr('content');
            var csrf_param = $('meta[name=csrf-param]').attr('content');
            $('form input[name="' + csrf_param + '"]').val(csrf_token);
          });
        }

      })(jQuery);
      /*!
       * jQuery Form Plugin
       * version: 3.32.0-2013.04.09
       * @requires jQuery v1.5 or later
       * Copyright (c) 2013 M. Alsup
       * Examples and documentation at: http://malsup.com/jquery/form/
       * Project repository: https://github.com/malsup/form
       * Dual licensed under the MIT and GPL licenses.
       * https://github.com/malsup/form#copyright-and-license
       */
      /*global ActiveXObject */

      ;
      (function ($) {
        "use strict";

        /*
    Usage Note:
    -----------
    Do not use both ajaxSubmit and ajaxForm on the same form.  These
    functions are mutually exclusive.  Use ajaxSubmit if you want
    to bind your own submit handler to the form.  For example,

    $(document).ready(function() {
        $('#myForm').on('submit', function(e) {
            e.preventDefault(); // <-- important
            $(this).ajaxSubmit({
                target: '#output'
            });
        });
    });

    Use ajaxForm when you want the plugin to manage all the event binding
    for you.  For example,

    $(document).ready(function() {
        $('#myForm').ajaxForm({
            target: '#output'
        });
    });

    You can also use ajaxForm with delegation (requires jQuery v1.7+), so the
    form does not have to exist when you invoke ajaxForm:

    $('#myForm').ajaxForm({
        delegation: true,
        target: '#output'
    });

    When using ajaxForm, the ajaxSubmit function will be invoked for you
    at the appropriate time.
*/

        /**
         * Feature detection
         */
        var feature = {};
        feature.fileapi = $("<input type='file'/>").get(0).files !== undefined;
        feature.formdata = window.FormData !== undefined;

        var hasProp = !! $.fn.prop;

        // attr2 uses prop when it can but checks the return type for
        // an expected string.  this accounts for the case where a form 
        // contains inputs with names like "action" or "method"; in those
        // cases "prop" returns the element
        $.fn.attr2 = function () {
          if (!hasProp) return this.attr.apply(this, arguments);
          var val = this.prop.apply(this, arguments);
          if ((val && val.jquery) || typeof val === 'string') return val;
          return this.attr.apply(this, arguments);
        };

        /**
         * ajaxSubmit() provides a mechanism for immediately submitting
         * an HTML form using AJAX.
         */
        $.fn.ajaxSubmit = function (options) {
          /*jshint scripturl:true */

          // fast fail if nothing selected (http://dev.jquery.com/ticket/2752)
          if (!this.length) {
            log('ajaxSubmit: skipping submit process - no element selected');
            return this;
          }

          var method, action, url, $form = this;

          if (typeof options == 'function') {
            options = {
              success: options
            };
          }

          method = this.attr2('method');
          action = this.attr2('action');

          url = (typeof action === 'string') ? $.trim(action) : '';
          url = url || window.location.href || '';
          if (url) {
            // clean url (don't include hash vaue)
            url = (url.match(/^([^#]+)/) || [])[1];
          }

          options = $.extend(true, {
            url: url,
            success: $.ajaxSettings.success,
            type: method || 'GET',
            iframeSrc: /^https/i.test(window.location.href || '') ? 'javascript:false' : 'about:blank'
          }, options);

          // hook for manipulating the form data before it is extracted;
          // convenient for use with rich editors like tinyMCE or FCKEditor
          var veto = {};
          this.trigger('form-pre-serialize', [this, options, veto]);
          if (veto.veto) {
            log('ajaxSubmit: submit vetoed via form-pre-serialize trigger');
            return this;
          }

          // provide opportunity to alter form data before it is serialized
          if (options.beforeSerialize && options.beforeSerialize(this, options) === false) {
            log('ajaxSubmit: submit aborted via beforeSerialize callback');
            return this;
          }

          var traditional = options.traditional;
          if (traditional === undefined) {
            traditional = $.ajaxSettings.traditional;
          }

          var elements = [];
          var qx, a = this.formToArray(options.semantic, elements);
          if (options.data) {
            options.extraData = options.data;
            qx = $.param(options.data, traditional);
          }

          // give pre-submit callback an opportunity to abort the submit
          if (options.beforeSubmit && options.beforeSubmit(a, this, options) === false) {
            log('ajaxSubmit: submit aborted via beforeSubmit callback');
            return this;
          }

          // fire vetoable 'validate' event
          this.trigger('form-submit-validate', [a, this, options, veto]);
          if (veto.veto) {
            log('ajaxSubmit: submit vetoed via form-submit-validate trigger');
            return this;
          }

          var q = $.param(a, traditional);
          if (qx) {
            q = (q ? (q + '&' + qx) : qx);
          }
          if (options.type.toUpperCase() == 'GET') {
            options.url += (options.url.indexOf('?') >= 0 ? '&' : '?') + q;
            options.data = null; // data is null for 'get'
          } else {
            options.data = q; // data is the query string for 'post'
          }

          var callbacks = [];
          if (options.resetForm) {
            callbacks.push(function () {
              $form.resetForm();
            });
          }
          if (options.clearForm) {
            callbacks.push(function () {
              $form.clearForm(options.includeHidden);
            });
          }

          // perform a load on the target only if dataType is not provided
          if (!options.dataType && options.target) {
            var oldSuccess = options.success ||
            function () {};
            callbacks.push(function (data) {
              var fn = options.replaceTarget ? 'replaceWith' : 'html';
              $(options.target)[fn](data).each(oldSuccess, arguments);
            });
          } else if (options.success) {
            callbacks.push(options.success);
          }

          options.success = function (data, status, xhr) { // jQuery 1.4+ passes xhr as 3rd arg
            var context = options.context || this; // jQuery 1.4+ supports scope context
            for (var i = 0, max = callbacks.length; i < max; i++) {
              callbacks[i].apply(context, [data, status, xhr || $form, $form]);
            }
          };

          // are there files to upload?
          // [value] (issue #113), also see comment:
          // https://github.com/malsup/form/commit/588306aedba1de01388032d5f42a60159eea9228#commitcomment-2180219
          var fileInputs = $('input[type=file]:enabled[value!=""]', this);

          var hasFileInputs = fileInputs.length > 0;
          var mp = 'multipart/form-data';
          var multipart = ($form.attr('enctype') == mp || $form.attr('encoding') == mp);

          var fileAPI = feature.fileapi && feature.formdata;
          log("fileAPI :" + fileAPI);
          var shouldUseFrame = (hasFileInputs || multipart) && !fileAPI;

          var jqxhr;

          // options.iframe allows user to force iframe mode
          // 06-NOV-09: now defaulting to iframe mode if file input is detected
          if (options.iframe !== false && (options.iframe || shouldUseFrame)) {
            // hack to fix Safari hang (thanks to Tim Molendijk for this)
            // see:  http://groups.google.com/group/jquery-dev/browse_thread/thread/36395b7ab510dd5d
            if (options.closeKeepAlive) {
              $.get(options.closeKeepAlive, function () {
                jqxhr = fileUploadIframe(a);
              });
            } else {
              jqxhr = fileUploadIframe(a);
            }
          } else if ((hasFileInputs || multipart) && fileAPI) {
            jqxhr = fileUploadXhr(a);
          } else {
            jqxhr = $.ajax(options);
          }

          $form.removeData('jqxhr').data('jqxhr', jqxhr);

          // clear element array
          for (var k = 0; k < elements.length; k++)
          elements[k] = null;

          // fire 'notify' event
          this.trigger('form-submit-notify', [this, options]);
          return this;

          // utility fn for deep serialization
          function deepSerialize(extraData) {
            var serialized = $.param(extraData).split('&');
            var len = serialized.length;
            var result = [];
            var i, part;
            for (i = 0; i < len; i++) {
              // #252; undo param space replacement
              serialized[i] = serialized[i].replace(/\+/g, ' ');
              part = serialized[i].split('=');
              // #278; use array instead of object storage, favoring array serializations
              result.push([decodeURIComponent(part[0]), decodeURIComponent(part[1])]);
            }
            return result;
          }

          // XMLHttpRequest Level 2 file uploads (big hat tip to francois2metz)
          function fileUploadXhr(a) {
            var formdata = new FormData();

            for (var i = 0; i < a.length; i++) {
              formdata.append(a[i].name, a[i].value);
            }

            if (options.extraData) {
              var serializedData = deepSerialize(options.extraData);
              for (i = 0; i < serializedData.length; i++)
              if (serializedData[i]) formdata.append(serializedData[i][0], serializedData[i][1]);
            }

            options.data = null;

            var s = $.extend(true, {}, $.ajaxSettings, options, {
              contentType: false,
              processData: false,
              cache: false,
              type: method || 'POST'
            });

            if (options.uploadProgress) {
              // workaround because jqXHR does not expose upload property
              s.xhr = function () {
                var xhr = jQuery.ajaxSettings.xhr();
                if (xhr.upload) {
                  xhr.upload.addEventListener('progress', function (event) {
                    var percent = 0;
                    var position = event.loaded || event.position; /*event.position is deprecated*/
                    var total = event.total;
                    if (event.lengthComputable) {
                      percent = Math.ceil(position / total * 100);
                    }
                    options.uploadProgress(event, position, total, percent);
                  }, false);
                }
                return xhr;
              };
            }

            s.data = null;
            var beforeSend = s.beforeSend;
            s.beforeSend = function (xhr, o) {
              o.data = formdata;
              if (beforeSend) beforeSend.call(this, xhr, o);
            };
            return $.ajax(s);
          }

          // private function for handling file uploads (hat tip to YAHOO!)
          function fileUploadIframe(a) {
            var form = $form[0],
              el, i, s, g, id, $io, io, xhr, sub, n, timedOut, timeoutHandle;
            var deferred = $.Deferred();

            if (a) {
              // ensure that every serialized input is still enabled
              for (i = 0; i < elements.length; i++) {
                el = $(elements[i]);
                if (hasProp) el.prop('disabled', false);
                else el.removeAttr('disabled');
              }
            }

            s = $.extend(true, {}, $.ajaxSettings, options);
            s.context = s.context || s;
            id = 'jqFormIO' + (new Date().getTime());
            if (s.iframeTarget) {
              $io = $(s.iframeTarget);
              n = $io.attr2('name');
              if (!n) $io.attr2('name', id);
              else id = n;
            } else {
              $io = $('<iframe name="' + id + '" src="' + s.iframeSrc + '" />');
              $io.css({
                position: 'absolute',
                top: '-1000px',
                left: '-1000px'
              });
            }
            io = $io[0];


            xhr = { // mock object
              aborted: 0,
              responseText: null,
              responseXML: null,
              status: 0,
              statusText: 'n/a',
              getAllResponseHeaders: function () {},
              getResponseHeader: function () {},
              setRequestHeader: function () {},
              abort: function (status) {
                var e = (status === 'timeout' ? 'timeout' : 'aborted');
                log('aborting upload... ' + e);
                this.aborted = 1;

                try { // #214, #257
                  if (io.contentWindow.document.execCommand) {
                    io.contentWindow.document.execCommand('Stop');
                  }
                } catch (ignore) {}

                $io.attr('src', s.iframeSrc); // abort op in progress
                xhr.error = e;
                if (s.error) s.error.call(s.context, xhr, e, status);
                if (g) $.event.trigger("ajaxError", [xhr, s, e]);
                if (s.complete) s.complete.call(s.context, xhr, e);
              }
            };

            g = s.global;
            // trigger ajax global events so that activity/block indicators work like normal
            if (g && 0 === $.active++) {
              $.event.trigger("ajaxStart");
            }
            if (g) {
              $.event.trigger("ajaxSend", [xhr, s]);
            }

            if (s.beforeSend && s.beforeSend.call(s.context, xhr, s) === false) {
              if (s.global) {
                $.active--;
              }
              deferred.reject();
              return deferred;
            }
            if (xhr.aborted) {
              deferred.reject();
              return deferred;
            }

            // add submitting element to data if we know it
            sub = form.clk;
            if (sub) {
              n = sub.name;
              if (n && !sub.disabled) {
                s.extraData = s.extraData || {};
                s.extraData[n] = sub.value;
                if (sub.type == "image") {
                  s.extraData[n + '.x'] = form.clk_x;
                  s.extraData[n + '.y'] = form.clk_y;
                }
              }
            }

            var CLIENT_TIMEOUT_ABORT = 1;
            var SERVER_ABORT = 2;

            function getDoc(frame) {
              /* it looks like contentWindow or contentDocument do not
               * carry the protocol property in ie8, when running under ssl
               * frame.document is the only valid response document, since
               * the protocol is know but not on the other two objects. strange?
               * "Same origin policy" http://en.wikipedia.org/wiki/Same_origin_policy
               */

              var doc = null;

              // IE8 cascading access check
              try {
                if (frame.contentWindow) {
                  doc = frame.contentWindow.document;
                }
              } catch (err) {
                // IE8 access denied under ssl & missing protocol
                log('cannot get iframe.contentWindow document: ' + err);
              }

              if (doc) { // successful getting content
                return doc;
              }

              try { // simply checking may throw in ie8 under ssl or mismatched protocol
                doc = frame.contentDocument ? frame.contentDocument : frame.document;
              } catch (err) {
                // last attempt
                log('cannot get iframe.contentDocument: ' + err);
                doc = frame.document;
              }
              return doc;
            }

            // Rails CSRF hack (thanks to Yvan Barthelemy)
            var csrf_token = $('meta[name=csrf-token]').attr('content');
            var csrf_param = $('meta[name=csrf-param]').attr('content');
            if (csrf_param && csrf_token) {
              s.extraData = s.extraData || {};
              s.extraData[csrf_param] = csrf_token;
            }

            // take a breath so that pending repaints get some cpu time before the upload starts
            function doSubmit() {
              // make sure form attrs are set
              var t = $form.attr2('target'),
                a = $form.attr2('action');

              // update form attrs in IE friendly way
              form.setAttribute('target', id);
              if (!method) {
                form.setAttribute('method', 'POST');
              }
              if (a != s.url) {
                form.setAttribute('action', s.url);
              }

              // ie borks in some cases when setting encoding
              if (!s.skipEncodingOverride && (!method || /post/i.test(method))) {
                $form.attr({
                  encoding: 'multipart/form-data',
                  enctype: 'multipart/form-data'
                });
              }

              // support timout
              if (s.timeout) {
                timeoutHandle = setTimeout(function () {
                  timedOut = true;
                  cb(CLIENT_TIMEOUT_ABORT);
                }, s.timeout);
              }

              // look for server aborts
              function checkState() {
                try {
                  var state = getDoc(io).readyState;
                  log('state = ' + state);
                  if (state && state.toLowerCase() == 'uninitialized') setTimeout(checkState, 50);
                } catch (e) {
                  log('Server abort: ', e, ' (', e.name, ')');
                  cb(SERVER_ABORT);
                  if (timeoutHandle) clearTimeout(timeoutHandle);
                  timeoutHandle = undefined;
                }
              }

              // add "extra" data to form if provided in options
              var extraInputs = [];
              try {
                if (s.extraData) {
                  for (var n in s.extraData) {
                    if (s.extraData.hasOwnProperty(n)) {
                      // if using the $.param format that allows for multiple values with the same name
                      if ($.isPlainObject(s.extraData[n]) && s.extraData[n].hasOwnProperty('name') && s.extraData[n].hasOwnProperty('value')) {
                        extraInputs.push(
                        $('<input type="hidden" name="' + s.extraData[n].name + '">').val(s.extraData[n].value).appendTo(form)[0]);
                      } else {
                        extraInputs.push(
                        $('<input type="hidden" name="' + n + '">').val(s.extraData[n]).appendTo(form)[0]);
                      }
                    }
                  }
                }

                if (!s.iframeTarget) {
                  // add iframe to doc and submit the form
                  $io.appendTo('body');
                  if (io.attachEvent) io.attachEvent('onload', cb);
                  else io.addEventListener('load', cb, false);
                }
                setTimeout(checkState, 15);

                try {
                  form.submit();
                } catch (err) {
                  // just in case form has element with name/id of 'submit'
                  var submitFn = document.createElement('form').submit;
                  submitFn.apply(form);
                }
              } finally {
                // reset attrs and remove "extra" input elements
                form.setAttribute('action', a);
                if (t) {
                  form.setAttribute('target', t);
                } else {
                  $form.removeAttr('target');
                }
                $(extraInputs).remove();
              }
            }

            if (s.forceSync) {
              doSubmit();
            } else {
              setTimeout(doSubmit, 10); // this lets dom updates render
            }

            var data, doc, domCheckCount = 50,
              callbackProcessed;

            function cb(e) {
              if (xhr.aborted || callbackProcessed) {
                return;
              }

              doc = getDoc(io);
              if (!doc) {
                log('cannot access response document');
                e = SERVER_ABORT;
              }
              if (e === CLIENT_TIMEOUT_ABORT && xhr) {
                xhr.abort('timeout');
                deferred.reject(xhr, 'timeout');
                return;
              } else if (e == SERVER_ABORT && xhr) {
                xhr.abort('server abort');
                deferred.reject(xhr, 'error', 'server abort');
                return;
              }

              if (!doc || doc.location.href == s.iframeSrc) {
                // response not received yet
                if (!timedOut) return;
              }
              if (io.detachEvent) io.detachEvent('onload', cb);
              else io.removeEventListener('load', cb, false);

              var status = 'success',
                errMsg;
              try {
                if (timedOut) {
                  throw 'timeout';
                }

                var isXml = s.dataType == 'xml' || doc.XMLDocument || $.isXMLDoc(doc);
                log('isXml=' + isXml);
                if (!isXml && window.opera && (doc.body === null || !doc.body.innerHTML)) {
                  if (--domCheckCount) {
                    // in some browsers (Opera) the iframe DOM is not always traversable when
                    // the onload callback fires, so we loop a bit to accommodate
                    log('requeing onLoad callback, DOM not available');
                    setTimeout(cb, 250);
                    return;
                  }
                  // let this fall through because server response could be an empty document
                  //log('Could not access iframe DOM after mutiple tries.');
                  //throw 'DOMException: not available';
                }

                //log('response detected');
                var docRoot = doc.body ? doc.body : doc.documentElement;
                xhr.responseText = docRoot ? docRoot.innerHTML : null;
                xhr.responseXML = doc.XMLDocument ? doc.XMLDocument : doc;
                if (isXml) s.dataType = 'xml';
                xhr.getResponseHeader = function (header) {
                  var headers = {
                    'content-type': s.dataType
                  };
                  return headers[header];
                };
                // support for XHR 'status' & 'statusText' emulation :
                if (docRoot) {
                  xhr.status = Number(docRoot.getAttribute('status')) || xhr.status;
                  xhr.statusText = docRoot.getAttribute('statusText') || xhr.statusText;
                }

                var dt = (s.dataType || '').toLowerCase();
                var scr = /(json|script|text)/.test(dt);
                if (scr || s.textarea) {
                  // see if user embedded response in textarea
                  var ta = doc.getElementsByTagName('textarea')[0];
                  if (ta) {
                    xhr.responseText = ta.value;
                    // support for XHR 'status' & 'statusText' emulation :
                    xhr.status = Number(ta.getAttribute('status')) || xhr.status;
                    xhr.statusText = ta.getAttribute('statusText') || xhr.statusText;
                  } else if (scr) {
                    // account for browsers injecting pre around json response
                    var pre = doc.getElementsByTagName('pre')[0];
                    var b = doc.getElementsByTagName('body')[0];
                    if (pre) {
                      xhr.responseText = pre.textContent ? pre.textContent : pre.innerText;
                    } else if (b) {
                      xhr.responseText = b.textContent ? b.textContent : b.innerText;
                    }
                  }
                } else if (dt == 'xml' && !xhr.responseXML && xhr.responseText) {
                  xhr.responseXML = toXml(xhr.responseText);
                }

                try {
                  data = httpData(xhr, dt, s);
                } catch (err) {
                  status = 'parsererror';
                  xhr.error = errMsg = (err || status);
                }
              } catch (err) {
                log('error caught: ', err);
                status = 'error';
                xhr.error = errMsg = (err || status);
              }

              if (xhr.aborted) {
                log('upload aborted');
                status = null;
              }

              if (xhr.status) { // we've set xhr.status
                status = (xhr.status >= 200 && xhr.status < 300 || xhr.status === 304) ? 'success' : 'error';
              }

              // ordering of these callbacks/triggers is odd, but that's how $.ajax does it
              if (status === 'success') {
                if (s.success) s.success.call(s.context, data, 'success', xhr);
                deferred.resolve(xhr.responseText, 'success', xhr);
                if (g) $.event.trigger("ajaxSuccess", [xhr, s]);
              } else if (status) {
                if (errMsg === undefined) errMsg = xhr.statusText;
                if (s.error) s.error.call(s.context, xhr, status, errMsg);
                deferred.reject(xhr, 'error', errMsg);
                if (g) $.event.trigger("ajaxError", [xhr, s, errMsg]);
              }

              if (g) $.event.trigger("ajaxComplete", [xhr, s]);

              if (g && !--$.active) {
                $.event.trigger("ajaxStop");
              }

              if (s.complete) s.complete.call(s.context, xhr, status);

              callbackProcessed = true;
              if (s.timeout) clearTimeout(timeoutHandle);

              // clean up
              setTimeout(function () {
                if (!s.iframeTarget) $io.remove();
                xhr.responseXML = null;
              }, 100);
            }

            var toXml = $.parseXML ||
            function (s, doc) { // use parseXML if available (jQuery 1.5+)
              if (window.ActiveXObject) {
                doc = new ActiveXObject('Microsoft.XMLDOM');
                doc.async = 'false';
                doc.loadXML(s);
              } else {
                doc = (new DOMParser()).parseFromString(s, 'text/xml');
              }
              return (doc && doc.documentElement && doc.documentElement.nodeName != 'parsererror') ? doc : null;
            };
            var parseJSON = $.parseJSON ||
            function (s) {
              /*jslint evil:true */
              return window['eval']('(' + s + ')');
            };

            var httpData = function (xhr, type, s) { // mostly lifted from jq1.4.4
                var ct = xhr.getResponseHeader('content-type') || '',
                  xml = type === 'xml' || !type && ct.indexOf('xml') >= 0,
                  data = xml ? xhr.responseXML : xhr.responseText;

                if (xml && data.documentElement.nodeName === 'parsererror') {
                  if ($.error) $.error('parsererror');
                }
                if (s && s.dataFilter) {
                  data = s.dataFilter(data, type);
                }
                if (typeof data === 'string') {
                  if (type === 'json' || !type && ct.indexOf('json') >= 0) {
                    data = parseJSON(data);
                  } else if (type === "script" || !type && ct.indexOf("javascript") >= 0) {
                    $.globalEval(data);
                  }
                }
                return data;
              };

            return deferred;
          }
        };

        /**
         * ajaxForm() provides a mechanism for fully automating form submission.
         *
         * The advantages of using this method instead of ajaxSubmit() are:
         *
         * 1: This method will include coordinates for <input type="image" /> elements (if the element
         *    is used to submit the form).
         * 2. This method will include the submit element's name/value data (for the element that was
         *    used to submit the form).
         * 3. This method binds the submit() method to the form for you.
         *
         * The options argument for ajaxForm works exactly as it does for ajaxSubmit.  ajaxForm merely
         * passes the options argument along after properly binding events for submit elements and
         * the form itself.
         */
        $.fn.ajaxForm = function (options) {
          options = options || {};
          options.delegation = options.delegation && $.isFunction($.fn.on);

          // in jQuery 1.3+ we can fix mistakes with the ready state
          if (!options.delegation && this.length === 0) {
            var o = {
              s: this.selector,
              c: this.context
            };
            if (!$.isReady && o.s) {
              log('DOM not ready, queuing ajaxForm');
              $(function () {
                $(o.s, o.c).ajaxForm(options);
              });
              return this;
            }
            // is your DOM ready?  http://docs.jquery.com/Tutorials:Introducing_$(document).ready()
            log('terminating; zero elements found by selector' + ($.isReady ? '' : ' (DOM not ready)'));
            return this;
          }

          if (options.delegation) {
            $(document).off('submit.form-plugin', this.selector, doAjaxSubmit).off('click.form-plugin', this.selector, captureSubmittingElement).on('submit.form-plugin', this.selector, options, doAjaxSubmit).on('click.form-plugin', this.selector, options, captureSubmittingElement);
            return this;
          }

          return this.ajaxFormUnbind().bind('submit.form-plugin', options, doAjaxSubmit).bind('click.form-plugin', options, captureSubmittingElement);
        };

        // private event handlers
        function doAjaxSubmit(e) {
          /*jshint validthis:true */
          var options = e.data;
          if (!e.isDefaultPrevented()) { // if event has been canceled, don't proceed
            e.preventDefault();
            $(this).ajaxSubmit(options);
          }
        }

        function captureSubmittingElement(e) {
          /*jshint validthis:true */
          var target = e.target;
          var $el = $(target);
          if (!($el.is("[type=submit],[type=image]"))) {
            // is this a child element of the submit el?  (ex: a span within a button)
            var t = $el.closest('[type=submit]');
            if (t.length === 0) {
              return;
            }
            target = t[0];
          }
          var form = this;
          form.clk = target;
          if (target.type == 'image') {
            if (e.offsetX !== undefined) {
              form.clk_x = e.offsetX;
              form.clk_y = e.offsetY;
            } else if (typeof $.fn.offset == 'function') {
              var offset = $el.offset();
              form.clk_x = e.pageX - offset.left;
              form.clk_y = e.pageY - offset.top;
            } else {
              form.clk_x = e.pageX - target.offsetLeft;
              form.clk_y = e.pageY - target.offsetTop;
            }
          }
          // clear form vars
          setTimeout(function () {
            form.clk = form.clk_x = form.clk_y = null;
          }, 100);
        }


        // ajaxFormUnbind unbinds the event handlers that were bound by ajaxForm
        $.fn.ajaxFormUnbind = function () {
          return this.unbind('submit.form-plugin click.form-plugin');
        };

        /**
         * formToArray() gathers form element data into an array of objects that can
         * be passed to any of the following ajax functions: $.get, $.post, or load.
         * Each object in the array has both a 'name' and 'value' property.  An example of
         * an array for a simple login form might be:
         *
         * [ { name: 'username', value: 'jresig' }, { name: 'password', value: 'secret' } ]
         *
         * It is this array that is passed to pre-submit callback functions provided to the
         * ajaxSubmit() and ajaxForm() methods.
         */
        $.fn.formToArray = function (semantic, elements) {
          var a = [];
          if (this.length === 0) {
            return a;
          }

          var form = this[0];
          var els = semantic ? form.getElementsByTagName('*') : form.elements;
          if (!els) {
            return a;
          }

          var i, j, n, v, el, max, jmax;
          for (i = 0, max = els.length; i < max; i++) {
            el = els[i];
            n = el.name;
            if (!n || el.disabled) {
              continue;
            }

            if (semantic && form.clk && el.type == "image") {
              // handle image inputs on the fly when semantic == true
              if (form.clk == el) {
                a.push({
                  name: n,
                  value: $(el).val(),
                  type: el.type
                });
                a.push({
                  name: n + '.x',
                  value: form.clk_x
                }, {
                  name: n + '.y',
                  value: form.clk_y
                });
              }
              continue;
            }

            v = $.fieldValue(el, true);
            if (v && v.constructor == Array) {
              if (elements) elements.push(el);
              for (j = 0, jmax = v.length; j < jmax; j++) {
                a.push({
                  name: n,
                  value: v[j]
                });
              }
            } else if (feature.fileapi && el.type == 'file') {
              if (elements) elements.push(el);
              var files = el.files;
              if (files.length) {
                for (j = 0; j < files.length; j++) {
                  a.push({
                    name: n,
                    value: files[j],
                    type: el.type
                  });
                }
              } else {
                // #180
                a.push({
                  name: n,
                  value: '',
                  type: el.type
                });
              }
            } else if (v !== null && typeof v != 'undefined') {
              if (elements) elements.push(el);
              a.push({
                name: n,
                value: v,
                type: el.type,
                required: el.required
              });
            }
          }

          if (!semantic && form.clk) {
            // input type=='image' are not found in elements array! handle it here
            var $input = $(form.clk),
              input = $input[0];
            n = input.name;
            if (n && !input.disabled && input.type == 'image') {
              a.push({
                name: n,
                value: $input.val()
              });
              a.push({
                name: n + '.x',
                value: form.clk_x
              }, {
                name: n + '.y',
                value: form.clk_y
              });
            }
          }
          return a;
        };

        /**
         * Serializes form data into a 'submittable' string. This method will return a string
         * in the format: name1=value1&amp;name2=value2
         */
        $.fn.formSerialize = function (semantic) {
          //hand off to jQuery.param for proper encoding
          return $.param(this.formToArray(semantic));
        };

        /**
         * Serializes all field elements in the jQuery object into a query string.
         * This method will return a string in the format: name1=value1&amp;name2=value2
         */
        $.fn.fieldSerialize = function (successful) {
          var a = [];
          this.each(function () {
            var n = this.name;
            if (!n) {
              return;
            }
            var v = $.fieldValue(this, successful);
            if (v && v.constructor == Array) {
              for (var i = 0, max = v.length; i < max; i++) {
                a.push({
                  name: n,
                  value: v[i]
                });
              }
            } else if (v !== null && typeof v != 'undefined') {
              a.push({
                name: this.name,
                value: v
              });
            }
          });
          //hand off to jQuery.param for proper encoding
          return $.param(a);
        };

        /**
         * Returns the value(s) of the element in the matched set.  For example, consider the following form:
         *
         *  <form><fieldset>
         *      <input name="A" type="text" />
         *      <input name="A" type="text" />
         *      <input name="B" type="checkbox" value="B1" />
         *      <input name="B" type="checkbox" value="B2"/>
         *      <input name="C" type="radio" value="C1" />
         *      <input name="C" type="radio" value="C2" />
         *  </fieldset></form>
         *
         *  var v = $('input[type=text]').fieldValue();
         *  // if no values are entered into the text inputs
         *  v == ['','']
         *  // if values entered into the text inputs are 'foo' and 'bar'
         *  v == ['foo','bar']
         *
         *  var v = $('input[type=checkbox]').fieldValue();
         *  // if neither checkbox is checked
         *  v === undefined
         *  // if both checkboxes are checked
         *  v == ['B1', 'B2']
         *
         *  var v = $('input[type=radio]').fieldValue();
         *  // if neither radio is checked
         *  v === undefined
         *  // if first radio is checked
         *  v == ['C1']
         *
         * The successful argument controls whether or not the field element must be 'successful'
         * (per http://www.w3.org/TR/html4/interact/forms.html#successful-controls).
         * The default value of the successful argument is true.  If this value is false the value(s)
         * for each element is returned.
         *
         * Note: This method *always* returns an array.  If no valid value can be determined the
         *    array will be empty, otherwise it will contain one or more values.
         */
        $.fn.fieldValue = function (successful) {
          for (var val = [], i = 0, max = this.length; i < max; i++) {
            var el = this[i];
            var v = $.fieldValue(el, successful);
            if (v === null || typeof v == 'undefined' || (v.constructor == Array && !v.length)) {
              continue;
            }
            if (v.constructor == Array) $.merge(val, v);
            else val.push(v);
          }
          return val;
        };

        /**
         * Returns the value of the field element.
         */
        $.fieldValue = function (el, successful) {
          var n = el.name,
            t = el.type,
            tag = el.tagName.toLowerCase();
          if (successful === undefined) {
            successful = true;
          }

          if (successful && (!n || el.disabled || t == 'reset' || t == 'button' || (t == 'checkbox' || t == 'radio') && !el.checked || (t == 'submit' || t == 'image') && el.form && el.form.clk != el || tag == 'select' && el.selectedIndex == -1)) {
            return null;
          }

          if (tag == 'select') {
            var index = el.selectedIndex;
            if (index < 0) {
              return null;
            }
            var a = [],
              ops = el.options;
            var one = (t == 'select-one');
            var max = (one ? index + 1 : ops.length);
            for (var i = (one ? index : 0); i < max; i++) {
              var op = ops[i];
              if (op.selected) {
                var v = op.value;
                if (!v) { // extra pain for IE...
                  v = (op.attributes && op.attributes['value'] && !(op.attributes['value'].specified)) ? op.text : op.value;
                }
                if (one) {
                  return v;
                }
                a.push(v);
              }
            }
            return a;
          }
          return $(el).val();
        };

        /**
         * Clears the form data.  Takes the following actions on the form's input fields:
         *  - input text fields will have their 'value' property set to the empty string
         *  - select elements will have their 'selectedIndex' property set to -1
         *  - checkbox and radio inputs will have their 'checked' property set to false
         *  - inputs of type submit, button, reset, and hidden will *not* be effected
         *  - button elements will *not* be effected
         */
        $.fn.clearForm = function (includeHidden) {
          return this.each(function () {
            $('input,select,textarea', this).clearFields(includeHidden);
          });
        };

        /**
         * Clears the selected form elements.
         */
        $.fn.clearFields = $.fn.clearInputs = function (includeHidden) {
          var re = /^(?:color|date|datetime|email|month|number|password|range|search|tel|text|time|url|week)$/i; // 'hidden' is not in this list
          return this.each(function () {
            var t = this.type,
              tag = this.tagName.toLowerCase();
            if (re.test(t) || tag == 'textarea') {
              this.value = '';
            } else if (t == 'checkbox' || t == 'radio') {
              this.checked = false;
            } else if (tag == 'select') {
              this.selectedIndex = -1;
            } else if (t == "file") {
              if (/MSIE/.test(navigator.userAgent)) {
                $(this).replaceWith($(this).clone(true));
              } else {
                $(this).val('');
              }
            } else if (includeHidden) {
              // includeHidden can be the value true, or it can be a selector string
              // indicating a special test; for example:
              //  $('#myForm').clearForm('.special:hidden')
              // the above would clean hidden inputs that have the class of 'special'
              if ((includeHidden === true && /hidden/.test(t)) || (typeof includeHidden == 'string' && $(this).is(includeHidden))) this.value = '';
            }
          });
        };

        /**
         * Resets the form data.  Causes all form elements to be reset to their original value.
         */
        $.fn.resetForm = function () {
          return this.each(function () {
            // guard against an input with the name of 'reset'
            // note that IE reports the reset function as an 'object'
            if (typeof this.reset == 'function' || (typeof this.reset == 'object' && !this.reset.nodeType)) {
              this.reset();
            }
          });
        };

        /**
         * Enables or disables any matching elements.
         */
        $.fn.enable = function (b) {
          if (b === undefined) {
            b = true;
          }
          return this.each(function () {
            this.disabled = !b;
          });
        };

        /**
         * Checks/unchecks any matching checkboxes or radio buttons and
         * selects/deselects and matching option elements.
         */
        $.fn.selected = function (select) {
          if (select === undefined) {
            select = true;
          }
          return this.each(function () {
            var t = this.type;
            if (t == 'checkbox' || t == 'radio') {
              this.checked = select;
            } else if (this.tagName.toLowerCase() == 'option') {
              var $sel = $(this).parent('select');
              if (select && $sel[0] && $sel[0].type == 'select-one') {
                // deselect all other options
                $sel.find('option').selected(false);
              }
              this.selected = select;
            }
          });
        };

        // expose debug var
        $.fn.ajaxSubmit.debug = false;

        // helper fn for console logging
        function log() {
          if (!$.fn.ajaxSubmit.debug) return;
          var msg = '[jquery.form] ' + Array.prototype.join.call(arguments, '');
          if (window.console && window.console.log) {
            window.console.log(msg);
          } else if (window.opera && window.opera.postError) {
            window.opera.postError(msg);
          }
        }

      })(jQuery);
      (function () {

        window.set_message = function (obj, message_type, message) {
          obj.parents(".set-block:first").find("." + message_type).remove();
          return obj.parents(".set-block:first").prepend("<div class='" + message_type + "'>" + message + "</div>");
        };

        window.add_commas = function (nStr) {
          var rgx, x, x1, x2;
          nStr += '';
          x = nStr.split('.');
          x1 = x[0];
          x2 = x.length > 1 ? "." + x[1] : "";
          rgx = /(\d+)(\d{3})/;
          while (rgx.test(x1)) {
            x1 = x1.replace(rgx, "$1&nbsp;$2");
          }
          return x1 + x2;
        };

        window.get_numeric = function (text) {
          if (text) {
            return Number(text.replace(/(?:,| |&nbsp;)/g, ""));
          } else {
            return 0;
          }
        };

      }).call(this);
      /*
       * Facebox (for jQuery)
       * version: 1.2 (05/05/2008)
       * @requires jQuery v1.2 or later
       *
       * Examples at http://famspam.com/facebox/
       *
       * Licensed under the MIT:
       *   http://www.opensource.org/licenses/mit-license.php
       *
       * Copyright 2007, 2008 Chris Wanstrath [ chris@ozmm.org ]
       *
       * Usage:
       *
       *  jQuery(document).ready(function() {
       *    jQuery('a[rel*=facebox]').facebox()
       *  })
       *
       *  <a href="#terms" rel="facebox">Terms</a>
       *    Loads the #terms div in the box
       *
       *  <a href="terms.html" rel="facebox">Terms</a>
       *    Loads the terms.html page in the box
       *
       *  <a href="terms.png" rel="facebox">Terms</a>
       *    Loads the terms.png image in the box
       *
       *
       *  You can also use it programmatically:
       *
       *    jQuery.facebox('some html')
       *
       *  The above will open a facebox with "some html" as the content.
       *
       *    jQuery.facebox(function($) {
       *      $.get('blah.html', function(data) { $.facebox(data) })
       *    })
       *
       *  The above will show a loading screen before the passed function is called,
       *  allowing for a better ajaxy experience.
       *
       *  The facebox function can also display an ajax page or image:
       *
       *    jQuery.facebox({ ajax: 'remote.html' })
       *    jQuery.facebox({ image: 'dude.jpg' })
       *
       *  Want to close the facebox?  Trigger the 'close.facebox' document event:
       *
       *    jQuery(document).trigger('close.facebox')
       *
       *  Facebox also has a bunch of other hooks:
       *
       *    loading.facebox
       *    beforeReveal.facebox
       *    reveal.facebox (aliased as 'afterReveal.facebox')
       *    init.facebox
       *
       *  Simply bind a function to any of these hooks:
       *
       *   $(document).bind('reveal.facebox', function() { ...stuff to do after the facebox and contents are revealed... })
       *
       */

       (function ($) {
        $.facebox = function (data, klass) {
          $.facebox.loading()

          if (data.ajax) fillFaceboxFromAjax(data.ajax, klass)
          else if (data.image) fillFaceboxFromImage(data.image, klass)
          else if (data.div) fillFaceboxFromHref(data.div, klass)
          else if ($.isFunction(data)) data.call($)
          else $.facebox.reveal(data, klass)
        }

        /*
         * Public, $.facebox methods
         */

        $.extend($.facebox, {
          settings: {
            opacity: 0,
            overlay: true,
            loadingImage: '/served_assets/facebox/loading.gif',
            closeImage: '/served_assets/facebox/closelabel.gif',
            imageTypes: ['png', 'jpg', 'jpeg', 'gif'],
            faceboxHtml: '\
    <div id="facebox" style="display:none;"> \
      <div class="popup"> \
        <table> \
          <tbody> \
            <tr> \
              <td class="tl"/><td class="b"/><td class="tr"/> \
            </tr> \
            <tr> \
              <td class="b"/> \
              <td class="body"> \
                <div class="content_fb"> \
                </div> \
                <div class="fb_footer"> \
                  <a href="#" class="close"> \
                    <img src="/served_assets/facebox/closelabel.gif" title="close" class="close_image" /> \
                  </a> \
                </div> \
              </td> \
              <td class="b"/> \
            </tr> \
            <tr> \
              <td class="bl"/><td class="b"/><td class="br"/> \
            </tr> \
          </tbody> \
        </table> \
      </div> \
    </div>'
          },

          loading: function () {
            init()
            if ($('#facebox .loading').length == 1) return true
            showOverlay()

            $('#facebox .content_fb').empty()
            $('#facebox .body').children().hide().end().
            append('<div class="loading"><img src="' + $.facebox.settings.loadingImage + '"/></div>')

            $('#facebox').css({
              top: getPageScroll()[1] + (getPageHeight() / 10),
              left: 385.5
            }).show()

            $(document).bind('keydown.facebox', function (e) {
              if (e.keyCode == 27) $.facebox.close()
              return true
            })
            $(document).trigger('loading.facebox')
          },

          reveal: function (data, klass) {
            $(document).trigger('beforeReveal.facebox')
            if (klass) $('#facebox .content_fb').addClass(klass)
            $('#facebox .content_fb').append(data)
            $('#facebox .loading').remove()
            $('#facebox .body').children().fadeIn('normal')
            $('#facebox').css('left', $(window).width() / 2 - ($('#facebox table').width() / 2))
            $(document).trigger('reveal.facebox').trigger('afterReveal.facebox')
          },

          close: function () {
            $(document).trigger('close.facebox')
            return false
          }
        })

        /*
         * Public, $.fn methods
         */

        $.fn.facebox = function (settings) {
          init(settings)

          function clickHandler() {
            $.facebox.loading(true)

            // support for rel="facebox.inline_popup" syntax, to add a class
            // also supports deprecated "facebox[.inline_popup]" syntax
            var klass = this.rel.match(/facebox\[?\.(\w+)\]?/)
            if (klass) klass = klass[1]

            fillFaceboxFromHref(this.href, klass)
            return false
          }

          return this.click(clickHandler)
        }

        /*
         * Private methods
         */

        // called one time to setup facebox on this page
        function init(settings) {
          if ($.facebox.settings.inited) return true
          else $.facebox.settings.inited = true

          $(document).trigger('init.facebox')
          makeCompatible()

          var imageTypes = $.facebox.settings.imageTypes.join('|')
          $.facebox.settings.imageTypesRegexp = new RegExp('\.' + imageTypes + '$', 'i')

          if (settings) $.extend($.facebox.settings, settings)
          $('body').append($.facebox.settings.faceboxHtml)

          var preload = [new Image(), new Image()]
          preload[0].src = $.facebox.settings.closeImage
          preload[1].src = $.facebox.settings.loadingImage

          $('#facebox').find('.b:first, .bl, .br, .tl, .tr').each(function () {
            preload.push(new Image())
            preload.slice(-1).src = $(this).css('background-image').replace(/url\((.+)\)/, '$1')
          })

          $('#facebox .close').click($.facebox.close)
          $('#facebox .close_image').attr('src', $.facebox.settings.closeImage)
        }

        // getPageScroll() by quirksmode.com
        function getPageScroll() {
          var xScroll, yScroll;
          if (self.pageYOffset) {
            yScroll = self.pageYOffset;
            xScroll = self.pageXOffset;
          } else if (document.documentElement && document.documentElement.scrollTop) { // Explorer 6 Strict
            yScroll = document.documentElement.scrollTop;
            xScroll = document.documentElement.scrollLeft;
          } else if (document.body) { // all other Explorers
            yScroll = document.body.scrollTop;
            xScroll = document.body.scrollLeft;
          }
          return new Array(xScroll, yScroll)
        }

        // Adapted from getPageSize() by quirksmode.com
        function getPageHeight() {
          var windowHeight
          if (self.innerHeight) { // all except Explorer
            windowHeight = self.innerHeight;
          } else if (document.documentElement && document.documentElement.clientHeight) { // Explorer 6 Strict Mode
            windowHeight = document.documentElement.clientHeight;
          } else if (document.body) { // other Explorers
            windowHeight = document.body.clientHeight;
          }
          return windowHeight
        }

        // Backwards compatibility
        function makeCompatible() {
          var $s = $.facebox.settings

          $s.loadingImage = $s.loading_image || $s.loadingImage
          $s.closeImage = $s.close_image || $s.closeImage
          $s.imageTypes = $s.image_types || $s.imageTypes
          $s.faceboxHtml = $s.facebox_html || $s.faceboxHtml
        }

        // Figures out what you want to display and displays it
        // formats are:
        //     div: #id
        //   image: blah.extension
        //    ajax: anything else
        function fillFaceboxFromHref(href, klass) {
          // div
          if (href.match(/#/)) {
            var url = window.location.href.split('#')[0]
            var target = href.replace(url, '')
            $.facebox.reveal($(target).clone().show(), klass)

            // image
          } else if (href.match($.facebox.settings.imageTypesRegexp)) {
            fillFaceboxFromImage(href, klass)
            // ajax
          } else {
            fillFaceboxFromAjax(href, klass)
          }
        }

        function fillFaceboxFromImage(href, klass) {
          var image = new Image()
          image.onload = function () {
              $.facebox.reveal('<div class="image"><img src="' + image.src + '" /></div>', klass)
            }
          image.src = href
        }

        function fillFaceboxFromAjax(href, klass) {
          $.get(href, function (data) {
            $.facebox.reveal(data, klass)
          })
        }

        function skipOverlay() {
          return $.facebox.settings.overlay == false || $.facebox.settings.opacity === null
        }

        function showOverlay() {
          if (skipOverlay()) return

          if ($('facebox_overlay').length == 0) $("body").append('<div id="facebox_overlay" class="facebox_hide"></div>')

          $('#facebox_overlay').hide().addClass("facebox_overlayBG").css('opacity', $.facebox.settings.opacity).click(function () {
            $(document).trigger('close.facebox')
          }).fadeIn(200)
          return false
        }

        function hideOverlay() {
          if (skipOverlay()) return

          $('#facebox_overlay').fadeOut(200, function () {
            $("#facebox_overlay").removeClass("facebox_overlayBG")
            $("#facebox_overlay").addClass("facebox_hide")
            $("#facebox_overlay").remove()
          })

          return false
        }

        /*
         * Bindings
         */

        $(document).bind('close.facebox', function () {
          $(document).unbind('keydown.facebox')
          $('#facebox').fadeOut(function () {
            $('#facebox .content_fb').removeClass().addClass('content_fb')
            hideOverlay()
            $('#facebox .loading').remove()
          })
        })

      })(jQuery);
      /*! Copyright (c) 2013 Brandon Aaron (http://brandonaaron.net)
       * Licensed under the MIT License (LICENSE.txt).
       *
       * Version 3.0.0
       */


       (function (factory) {
        if (typeof define === 'function' && define.amd) {
          // AMD. Register as an anonymous module.
          define(['jquery'], factory);
        } else {
          // Browser globals
          factory(jQuery);
        }
      }(function ($) {
        $.fn.bgiframe = function (s) {
          s = $.extend({
            top: 'auto',
            // auto == borderTopWidth
            left: 'auto',
            // auto == borderLeftWidth
            width: 'auto',
            // auto == offsetWidth
            height: 'auto',
            // auto == offsetHeight
            opacity: true,
            src: 'javascript:false;',
            conditional: /MSIE 6.0/.test(navigator.userAgent) // expresion or function. return false to prevent iframe insertion
          }, s);

          // wrap conditional in a function if it isn't already
          if (!$.isFunction(s.conditional)) {
            var condition = s.conditional;
            s.conditional = function () {
              return condition;
            };
          }

          var $iframe = $('<iframe class="bgiframe"frameborder="0"tabindex="-1"src="' + s.src + '"' + 'style="display:block;position:absolute;z-index:-1;"/>');

          return this.each(function () {
            var $this = $(this);
            if (s.conditional(this) === false) {
              return;
            }
            var existing = $this.children('iframe.bgiframe');
            var $el = existing.length === 0 ? $iframe.clone() : existing;
            $el.css({
              'top': s.top == 'auto' ? ((parseInt($this.css('borderTopWidth'), 10) || 0) * -1) + 'px' : prop(s.top),
              'left': s.left == 'auto' ? ((parseInt($this.css('borderLeftWidth'), 10) || 0) * -1) + 'px' : prop(s.left),
              'width': s.width == 'auto' ? (this.offsetWidth + 'px') : prop(s.width),
              'height': s.height == 'auto' ? (this.offsetHeight + 'px') : prop(s.height),
              'opacity': s.opacity === true ? 0 : undefined
            });

            if (existing.length === 0) {
              $this.prepend($el);
            }
          });
        };

        // old alias
        $.fn.bgIframe = $.fn.bgiframe;

        function prop(n) {
          return n && n.constructor === Number ? n + 'px' : n;
        }

      }));
      jQuery(function ($) {
        $(".buy_button").click(function (e) {
          e.preventDefault();
          var form = $(this).parents("form:first");
          addOrderItem(form);
        });

        $(".buy_form").submit(function (e) {
          e.preventDefault();
          var form = $(this);
          addOrderItem(form);
        });

        $(document).bind("ajaxSend", function () {
          own_preloader(true);
        }).bind("ajaxComplete", function () {
          own_preloader(false);
        });
      });

      function addOrderItem(form) {
        var fields = form.serialize();
        var path = form.attr("action").split("?");
        var url = path[0] + ".json";
        var lang = path[1] ? "?" + path[1] : "";
        path = url + lang;
        $.ajax({
          url: path,
          type: 'post',
          data: fields,
          dataType: 'json',
          success: function (response) {
            $("#cart_total_price").html(InSales.formatMoney(response.total_price, response.currency_format));
            $("#cart_items_count").html(response.items_count);
          },
          error: function (response) {}
        });
      }

      function changeCss(OBJ) {
        var imageHeight = OBJ.height();
        var imageWidth = OBJ.width();
        var windowWidth = $(window).width();
        var windowHeight = $(window).height();
        OBJ.css({
          "position": "absolute",
          "left": windowWidth / 2 - imageWidth / 2,
          "top": getPageScroll()[1] + (getPageHeight() / 2)
        });
      };


      // getPageScroll() by quirksmode.com
      function getPageScroll() {
        var xScroll, yScroll;
        if (self.pageYOffset) {
          yScroll = self.pageYOffset;
          xScroll = self.pageXOffset;
        } else if (document.documentElement && document.documentElement.scrollTop) { // Explorer 6 Strict
          yScroll = document.documentElement.scrollTop;
          xScroll = document.documentElement.scrollLeft;
        } else if (document.body) { // all other Explorers
          yScroll = document.body.scrollTop;
          xScroll = document.body.scrollLeft;
        }
        return new Array(xScroll, yScroll)
      }

      // Adapted from getPageSize() by quirksmode.com
      function getPageHeight() {
        var windowHeight
        if (self.innerHeight) { // all except Explorer
          windowHeight = self.innerHeight;
        } else if (document.documentElement && document.documentElement.clientHeight) { // Explorer 6 Strict Mode
          windowHeight = document.documentElement.clientHeight;
        } else if (document.body) { // other Explorers
          windowHeight = document.body.clientHeight;
        }
        return windowHeight
      }

      function own_preloader(event) {
        if (event == true) {
          if (!($("#own_preloader").attr("id"))) {
            preloader = '<div id="own_preloader" style="z-index:1000; width:32px; height:32px;"><img src="/served_assets/loading.gif"/></div>';
            $("body").append(preloader);
          }
          preloader = $("#own_preloader");
          preloader.show();

          changeCss(preloader);
          $(window).bind("resize", function () {
            changeCss(preloader);
          });
          $(window).bind("scroll", function () {
            changeCss(preloader);
          });
        } else {
          $(window).unbind("resize");
          $(window).unbind("scroll");
          if (typeof (preloader) != 'undefined') preloader.hide();
        }
      };
      /*
       * jQuery Autocomplete plugin 1.1
       *
       * Copyright (c) 2009 Jörn Zaefferer
       *
       * Dual licensed under the MIT and GPL licenses:
       *   http://www.opensource.org/licenses/mit-license.php
       *   http://www.gnu.org/licenses/gpl.html
       *
       * Revision: $Id: jquery.autocomplete.js 15 2009-08-22 10:30:27Z joern.zaefferer $
       */


      ;
      (function ($) {

        $.fn.extend({
          autocomplete: function (urlOrData, options) {
            var isUrl = typeof urlOrData == "string";
            options = $.extend({}, $.Autocompleter.defaults, {
              url: isUrl ? urlOrData : null,
              data: isUrl ? null : urlOrData,
              delay: isUrl ? $.Autocompleter.defaults.delay : 10,
              max: options && !options.scroll ? 10 : 150
            }, options);

            // if highlight is set to false, replace it with a do-nothing function
            options.highlight = options.highlight ||
            function (value) {
              return value;
            };

            // if the formatMatch option is not specified, then use formatItem for backwards compatibility
            options.formatMatch = options.formatMatch || options.formatItem;

            return this.each(function () {
              new $.Autocompleter(this, options);
            });
          },
          result: function (handler) {
            return this.bind("result", handler);
          },
          search: function (handler) {
            return this.trigger("search", [handler]);
          },
          flushCache: function () {
            return this.trigger("flushCache");
          },
          setOptions: function (options) {
            return this.trigger("setOptions", [options]);
          },
          unautocomplete: function () {
            return this.trigger("unautocomplete");
          }
        });

        $.Autocompleter = function (input, options) {

          var KEY = {
            UP: 38,
            DOWN: 40,
            DEL: 46,
            TAB: 9,
            RETURN: 13,
            ESC: 27,
            COMMA: 188,
            PAGEUP: 33,
            PAGEDOWN: 34,
            BACKSPACE: 8
          };

          // Create $ object for input element
          var $input = $(input).attr("autocomplete", "off").addClass(options.inputClass);

          var timeout;
          var previousValue = "";
          var cache = $.Autocompleter.Cache(options);
          var hasFocus = 0;
          var lastKeyPressCode;
          var config = {
            mouseDownOnSelect: false
          };
          var select = $.Autocompleter.Select(options, input, selectCurrent, config);

          var blockSubmit;

          // prevent form submit in opera when selecting with return key
          // $.browser.opera && $(input.form).bind("submit.autocomplete", function() {
          // 	if (blockSubmit) {
          // 		blockSubmit = false;
          // 		return false;
          // 	}
          // });
          $input.bind('keydown.autocomplete', function (event) {
            // a keypress means the input has focus
            // avoids issue where input had focus before the autocomplete was applied
            hasFocus = 1;
            // track last key pressed
            lastKeyPressCode = event.keyCode;
            switch (event.keyCode) {

            case KEY.UP:
              event.preventDefault();
              if (select.visible()) {
                select.prev();
              } else {
                onChange(0, true);
              }
              break;

            case KEY.DOWN:
              event.preventDefault();
              if (select.visible()) {
                select.next();
              } else {
                onChange(0, true);
              }
              break;

            case KEY.PAGEUP:
              event.preventDefault();
              if (select.visible()) {
                select.pageUp();
              } else {
                onChange(0, true);
              }
              break;

            case KEY.PAGEDOWN:
              event.preventDefault();
              if (select.visible()) {
                select.pageDown();
              } else {
                onChange(0, true);
              }
              break;

              // matches also semicolon
            case options.multiple && $.trim(options.multipleSeparator) == "," && KEY.COMMA:
            case KEY.TAB:
            case KEY.RETURN:
              if (selectCurrent()) {
                // stop default to prevent a form submit, Opera needs special handling
                event.preventDefault();
                blockSubmit = true;
                return false;
              }
              break;

            case KEY.ESC:
              select.hide();
              break;

            default:
              clearTimeout(timeout);
              timeout = setTimeout(onChange, options.delay);
              break;
            }
          }).focus(function () {
            // track whether the field has focus, we shouldn't process any
            // results if the field no longer has focus
            hasFocus++;
          }).blur(function () {
            hasFocus = 0;
            if (!config.mouseDownOnSelect) {
              hideResults();
            }
          }).click(function () {
            // show select when clicking in a focused field
            if (hasFocus++ > 1 && !select.visible()) {
              onChange(0, true);
            }
          }).bind("search", function () {
            // TODO why not just specifying both arguments?
            var fn = (arguments.length > 1) ? arguments[1] : null;

            function findValueCallback(q, data) {
              var result;
              if (data && data.length) {
                for (var i = 0; i < data.length; i++) {
                  if (data[i].result.toLowerCase() == q.toLowerCase()) {
                    result = data[i];
                    break;
                  }
                }
              }
              if (typeof fn == "function") fn(result);
              else $input.trigger("result", result && [result.data, result.value]);
            }
            $.each(trimWords($input.val()), function (i, value) {
              request(value, findValueCallback, findValueCallback);
            });
          }).bind("flushCache", function () {
            cache.flush();
          }).bind("setOptions", function () {
            $.extend(options, arguments[1]);
            // if we've updated the data, repopulate
            if ("data" in arguments[1]) cache.populate();
          }).bind("unautocomplete", function () {
            select.unbind();
            $input.unbind();
            $(input.form).unbind(".autocomplete");
          });


          function selectCurrent() {
            var selected = select.selected();
            if (!selected) return false;

            var v = selected.result;
            previousValue = v;

            if (options.multiple) {
              var words = trimWords($input.val());
              if (words.length > 1) {
                var seperator = options.multipleSeparator.length;
                var cursorAt = $(input).selection().start;
                var wordAt, progress = 0;
                $.each(words, function (i, word) {
                  progress += word.length;
                  if (cursorAt <= progress) {
                    wordAt = i;
                    return false;
                  }
                  progress += seperator;
                });
                words[wordAt] = v;
                // TODO this should set the cursor to the right position, but it gets overriden somewhere
                //$.Autocompleter.Selection(input, progress + seperator, progress + seperator);
                v = words.join(options.multipleSeparator);
              }
              v += options.multipleSeparator;
            }

            $input.val(v);
            hideResultsNow();
            $input.trigger("result", [selected.data, selected.value]);
            return true;
          }

          function onChange(crap, skipPrevCheck) {
            if (lastKeyPressCode == KEY.DEL) {
              select.hide();
              return;
            }

            var currentValue = $input.val();

            if (!skipPrevCheck && currentValue == previousValue) return;

            previousValue = currentValue;

            currentValue = lastWord(currentValue);
            if (currentValue.length >= options.minChars) {
              $input.addClass(options.loadingClass);
              if (!options.matchCase) currentValue = currentValue.toLowerCase();
              request(currentValue, receiveData, hideResultsNow);
            } else {
              stopLoading();
              select.hide();
            }
          };

          function trimWords(value) {
            if (!value) return [""];
            if (!options.multiple) return [$.trim(value)];
            return $.map(value.split(options.multipleSeparator), function (word) {
              return $.trim(value).length ? $.trim(word) : null;
            });
          }

          function lastWord(value) {
            if (!options.multiple) return value;
            var words = trimWords(value);
            if (words.length == 1) return words[0];
            var cursorAt = $(input).selection().start;
            if (cursorAt == value.length) {
              words = trimWords(value)
            } else {
              words = trimWords(value.replace(value.substring(cursorAt), ""));
            }
            return words[words.length - 1];
          }

          // fills in the input box w/the first match (assumed to be the best match)
          // q: the term entered
          // sValue: the first matching result
          function autoFill(q, sValue) {
            // autofill in the complete box w/the first match as long as the user hasn't entered in more data
            // if the last user key pressed was backspace, don't autofill
            if (options.autoFill && (lastWord($input.val()).toLowerCase() == q.toLowerCase()) && lastKeyPressCode != KEY.BACKSPACE) {
              // fill in the value (keep the case the user has typed)
              $input.val($input.val() + sValue.substring(lastWord(previousValue).length));
              // select the portion of the value not typed by the user (so the next character will erase)
              $(input).selection(previousValue.length, previousValue.length + sValue.length);
            }
          };

          function hideResults() {
            clearTimeout(timeout);
            timeout = setTimeout(hideResultsNow, 200);
          };

          function hideResultsNow() {
            var wasVisible = select.visible();
            select.hide();
            clearTimeout(timeout);
            stopLoading();
            if (options.mustMatch) {
              // call search and run callback
              $input.search(

              function (result) {
                // if no value found, clear the input box
                if (!result) {
                  if (options.multiple) {
                    var words = trimWords($input.val()).slice(0, -1);
                    $input.val(words.join(options.multipleSeparator) + (words.length ? options.multipleSeparator : ""));
                  } else {
                    $input.val("");
                    $input.trigger("result", null);
                  }
                }
              });
            }
          };

          function receiveData(q, data) {
            if (data && data.length && hasFocus) {
              stopLoading();
              select.display(data, q);
              autoFill(q, data[0].value);
              select.show();
            } else {
              hideResultsNow();
            }
          };

          function request(term, success, failure) {
            if (!options.matchCase) term = term.toLowerCase();
            var data = cache.load(term);
            // recieve the cached data
            if (data && data.length) {
              success(term, data);
              // if an AJAX url has been supplied, try loading the data now
            } else if ((typeof options.url == "string") && (options.url.length > 0)) {

              var extraParams = {
                timestamp: +new Date()
              };
              $.each(options.extraParams, function (key, param) {
                extraParams[key] = typeof param == "function" ? param() : param;
              });

              $.ajax({
                // try to leverage ajaxQueue plugin to abort previous requests
                mode: "abort",
                // limit abortion to this input
                port: "autocomplete" + input.name,
                dataType: options.dataType,
                url: options.url,
                data: $.extend({
                  q: lastWord(term),
                  limit: options.max
                }, extraParams),
                success: function (data) {
                  var parsed = options.parse && options.parse(data) || parse(data);
                  cache.add(term, parsed);
                  success(term, parsed);
                }
              });
            } else {
              // if we have a failure, we need to empty the list -- this prevents the the [TAB] key from selecting the last successful match
              select.emptyList();
              failure(term);
            }
          };

          function parse(data) {
            var parsed = [];
            var rows = data.split("\n");
            for (var i = 0; i < rows.length; i++) {
              var row = $.trim(rows[i]);
              if (row) {
                row = row.split("|");
                parsed[parsed.length] = {
                  data: row,
                  value: row[0],
                  result: options.formatResult && options.formatResult(row, row[0]) || row[0]
                };
              }
            }
            return parsed;
          };

          function stopLoading() {
            $input.removeClass(options.loadingClass);
          };

        };

        $.Autocompleter.defaults = {
          inputClass: "ac_input",
          resultsClass: "ac_results",
          loadingClass: "ac_loading",
          minChars: 1,
          delay: 400,
          matchCase: false,
          matchSubset: true,
          matchContains: false,
          cacheLength: 10,
          max: 100,
          mustMatch: false,
          extraParams: {},
          selectFirst: true,
          formatItem: function (row) {
            return row[0];
          },
          formatMatch: null,
          autoFill: false,
          width: 0,
          multiple: false,
          multipleSeparator: ", ",
          highlight: function (value, term) {
            return value.replace(new RegExp("(?![^&;]+;)(?!<[^<>]*)(" + term.replace(/([\^\$\(\)\[\]\{\}\*\.\+\?\|\\])/gi, "\\$1") + ")(?![^<>]*>)(?![^&;]+;)", "gi"), "<strong>$1</strong>");
          },
          scroll: true,
          scrollHeight: 180
        };

        $.Autocompleter.Cache = function (options) {

          var data = {};
          var length = 0;

          function matchSubset(s, sub) {
            if (!options.matchCase) s = s.toLowerCase();
            var i = s.indexOf(sub);
            if (options.matchContains == "word") {
              i = s.toLowerCase().search("\\b" + sub.toLowerCase());
            }
            if (i == -1) return false;
            return i == 0 || options.matchContains;
          };

          function add(q, value) {
            if (length > options.cacheLength) {
              flush();
            }
            if (!data[q]) {
              length++;
            }
            data[q] = value;
          }

          function populate() {
            if (!options.data) return false;
            // track the matches
            var stMatchSets = {},
              nullData = 0;

            // no url was specified, we need to adjust the cache length to make sure it fits the local data store
            if (!options.url) options.cacheLength = 1;

            // track all options for minChars = 0
            stMatchSets[""] = [];

            // loop through the array and create a lookup structure
            for (var i = 0, ol = options.data.length; i < ol; i++) {
              var rawValue = options.data[i];
              // if rawValue is a string, make an array otherwise just reference the array
              rawValue = (typeof rawValue == "string") ? [rawValue] : rawValue;

              var value = options.formatMatch(rawValue, i + 1, options.data.length);
              if (value === false) continue;

              var firstChar = value.charAt(0).toLowerCase();
              // if no lookup array for this character exists, look it up now
              if (!stMatchSets[firstChar]) stMatchSets[firstChar] = [];

              // if the match is a string
              var row = {
                value: value,
                data: rawValue,
                result: options.formatResult && options.formatResult(rawValue) || value
              };

              // push the current match into the set list
              stMatchSets[firstChar].push(row);

              // keep track of minChars zero items
              if (nullData++ < options.max) {
                stMatchSets[""].push(row);
              }
            };

            // add the data items to the cache
            $.each(stMatchSets, function (i, value) {
              // increase the cache size
              options.cacheLength++;
              // add to the cache
              add(i, value);
            });
          }

          // populate any existing data
          setTimeout(populate, 25);

          function flush() {
            data = {};
            length = 0;
          }

          return {
            flush: flush,
            add: add,
            populate: populate,
            load: function (q) {
              if (!options.cacheLength || !length) return null;
              /* 
               * if dealing w/local data and matchContains than we must make sure
               * to loop through all the data collections looking for matches
               */
              if (!options.url && options.matchContains) {
                // track all matches
                var csub = [];
                // loop through all the data grids for matches
                for (var k in data) {
                  // don't search through the stMatchSets[""] (minChars: 0) cache
                  // this prevents duplicates
                  if (k.length > 0) {
                    var c = data[k];
                    $.each(c, function (i, x) {
                      // if we've got a match, add it to the array
                      if (matchSubset(x.value, q)) {
                        csub.push(x);
                      }
                    });
                  }
                }
                return csub;
              } else
              // if the exact item exists, use it
              if (data[q]) {
                return data[q];
              } else if (options.matchSubset) {
                for (var i = q.length - 1; i >= options.minChars; i--) {
                  var c = data[q.substr(0, i)];
                  if (c) {
                    var csub = [];
                    $.each(c, function (i, x) {
                      if (matchSubset(x.value, q)) {
                        csub[csub.length] = x;
                      }
                    });
                    return csub;
                  }
                }
              }
              return null;
            }
          };
        };

        $.Autocompleter.Select = function (options, input, select, config) {
          var CLASSES = {
            ACTIVE: "ac_over"
          };

          var listItems, active = -1,
            data, term = "",
            needsInit = true,
            element, list;

          // Create results
          function init() {
            if (!needsInit) return;
            element = $("<div/>").hide().addClass(options.resultsClass).css("position", "absolute").appendTo(document.body);

            list = $("<ul/>").appendTo(element).mouseover(function (event) {
              if (target(event).nodeName && target(event).nodeName.toUpperCase() == 'LI') {
                active = $("li", list).removeClass(CLASSES.ACTIVE).index(target(event));
                $(target(event)).addClass(CLASSES.ACTIVE);
              }
            }).click(function (event) {
              $(target(event)).addClass(CLASSES.ACTIVE);
              select();
              // TODO provide option to avoid setting focus again after selection? useful for cleanup-on-focus
              input.focus();
              return false;
            }).mousedown(function () {
              config.mouseDownOnSelect = true;
            }).mouseup(function () {
              config.mouseDownOnSelect = false;
            });

            if (options.width > 0) element.css("width", options.width);

            needsInit = false;
          }

          function target(event) {
            var element = event.target;
            while (element && element.tagName != "LI")
            element = element.parentNode;
            // more fun with IE, sometimes event.target is empty, just ignore it then
            if (!element) return [];
            return element;
          }

          function moveSelect(step) {
            listItems.slice(active, active + 1).removeClass(CLASSES.ACTIVE);
            movePosition(step);
            var activeItem = listItems.slice(active, active + 1).addClass(CLASSES.ACTIVE);
            if (options.scroll) {
              var offset = 0;
              listItems.slice(0, active).each(function () {
                offset += this.offsetHeight;
              });
              if ((offset + activeItem[0].offsetHeight - list.scrollTop()) > list[0].clientHeight) {
                list.scrollTop(offset + activeItem[0].offsetHeight - list.innerHeight());
              } else if (offset < list.scrollTop()) {
                list.scrollTop(offset);
              }
            }
          };

          function movePosition(step) {
            active += step;
            if (active < 0) {
              active = listItems.size() - 1;
            } else if (active >= listItems.size()) {
              active = 0;
            }
          }

          function limitNumberOfItems(available) {
            return options.max && options.max < available ? options.max : available;
          }

          function fillList() {
            list.empty();
            var max = limitNumberOfItems(data.length);
            for (var i = 0; i < max; i++) {
              if (!data[i]) continue;
              var formatted = options.formatItem(data[i].data, i + 1, max, data[i].value, term);
              if (formatted === false) continue;
              var li = $("<li/>").html(options.highlight(formatted, term)).addClass(i % 2 == 0 ? "ac_even" : "ac_odd").appendTo(list)[0];
              $.data(li, "ac_data", data[i]);
            }
            listItems = list.find("li");
            if (options.selectFirst) {
              listItems.slice(0, 1).addClass(CLASSES.ACTIVE);
              active = 0;
            }
            // apply bgiframe if available
            if ($.fn.bgiframe) list.bgiframe();
          }

          return {
            display: function (d, q) {
              init();
              data = d;
              term = q;
              fillList();
            },
            next: function () {
              moveSelect(1);
            },
            prev: function () {
              moveSelect(-1);
            },
            pageUp: function () {
              if (active != 0 && active - 8 < 0) {
                moveSelect(-active);
              } else {
                moveSelect(-8);
              }
            },
            pageDown: function () {
              if (active != listItems.size() - 1 && active + 8 > listItems.size()) {
                moveSelect(listItems.size() - 1 - active);
              } else {
                moveSelect(8);
              }
            },
            hide: function () {
              element && element.hide();
              listItems && listItems.removeClass(CLASSES.ACTIVE);
              active = -1;
            },
            visible: function () {
              return element && element.is(":visible");
            },
            current: function () {
              return this.visible() && (listItems.filter("." + CLASSES.ACTIVE)[0] || options.selectFirst && listItems[0]);
            },
            show: function () {
              var offset = $(input).offset();
              element.css({
                width: typeof options.width == "string" || options.width > 0 ? options.width : $(input).width(),
                top: offset.top + input.offsetHeight,
                left: offset.left
              }).show();
              if (options.scroll) {
                list.scrollTop(0);
                list.css({
                  maxHeight: options.scrollHeight,
                  overflow: 'auto'
                });

                // if($.browser.msie && typeof document.body.style.maxHeight === "undefined") {
                // 	var listHeight = 0;
                // 	listItems.each(function() {
                // 		listHeight += this.offsetHeight;
                // 	});
                // 	var scrollbarsVisible = listHeight > options.scrollHeight;
                // 	list.css('height', scrollbarsVisible ? options.scrollHeight : listHeight );
                // 	if (!scrollbarsVisible) {
                // 		// IE doesn't recalculate width when scrollbar disappears
                // 		listItems.width( list.width() - parseInt(listItems.css("padding-left")) - parseInt(listItems.css("padding-right")) );
                // 	}
                // }
              }
            },
            selected: function () {
              var selected = listItems && listItems.filter("." + CLASSES.ACTIVE).removeClass(CLASSES.ACTIVE);
              return selected && selected.length && $.data(selected[0], "ac_data");
            },
            emptyList: function () {
              list && list.empty();
            },
            unbind: function () {
              element && element.remove();
            }
          };
        };

        $.fn.selection = function (start, end) {
          if (start !== undefined) {
            return this.each(function () {
              if (this.createTextRange) {
                var selRange = this.createTextRange();
                if (end === undefined || start == end) {
                  selRange.move("character", start);
                  selRange.select();
                } else {
                  selRange.collapse(true);
                  selRange.moveStart("character", start);
                  selRange.moveEnd("character", end);
                  selRange.select();
                }
              } else if (this.setSelectionRange) {
                this.setSelectionRange(start, end);
              } else if (this.selectionStart) {
                this.selectionStart = start;
                this.selectionEnd = end;
              }
            });
          }
          var field = this[0];
          if (field.createTextRange) {
            var range = document.selection.createRange(),
              orig = field.value,
              teststring = "<->",
              textLength = range.text.length;
            range.text = teststring;
            var caretAt = field.value.indexOf(teststring);
            field.value = orig;
            this.selection(caretAt, caretAt + textLength);
            return {
              start: caretAt,
              end: caretAt + textLength
            }
          } else if (field.selectionStart !== undefined) {
            return {
              start: field.selectionStart,
              end: field.selectionEnd
            }
          }
        };

      })(jQuery);

      if (window.deferreds == undefined) {
        window.deferreds = {};
      }

      function no_delivery(check_box) {
        var address_elements = $('#delivery_address input, #delivery_address textarea, #delivery_address select');
        var address_labels = $('#delivery_address label');
        if (check_box.prop('checked')) {
          address_elements.prop('disabled', true);
          check_box.removeAttr('disabled');
          address_labels.fadeTo("fast", 0.5);
        } else {
          address_elements.removeAttr('disabled');
          address_labels.fadeTo("fast", 1);
        }
      }

      function cities_autocomplete(object_klass, region_input_description) {
        var country_input_id = object_klass + '_country';
        var region_input_id = object_klass + '_state';
        var city_input_id = object_klass + '_city';
        var region_input_name = object_klass + '[state]';
        var kladr_host = 'http://kladr.insales.ru';
        var input_class = '';

        this.start = function () {
          if ($('#' + region_input_id).is('input')) {
            input_class = $('#' + region_input_id).attr("class");
            // Автодополнение не будет работать если не задан регион
            $(document).on('change', '#' + country_input_id, function () {
              process_region_field();
            });
            $(document).on('change', '#' + region_input_id, function () {
              process_city_field();
            });

            process_region_field();
          }
        }

        this.process_region_field = function () {
          var country = $("#" + country_input_id).val();

          if (country && $.inArray(country, ['RU', 'KZ', 'UA']) == -1) {
            var region_input = $('#' + region_input_id);
            var input = '<input id="' + region_input_id + '" name="' + region_input_name + '" type="text" class="' + input_class + '" value="" />';
            region_input.replaceWith(input);
          } else {
            fill_regions();
          }
        }

        this.process_city_field = function () {
          var country = $("#" + country_input_id).val();
          if (country && $.inArray(country, ['RU', 'KZ', 'UA']) == -1) return;

          var city_input = $('#' + city_input_id);
          var region = $('#' + region_input_id).val();

          var url = kladr_host + '/children.json?country=' + country + '&with_districts=1&region=' + region;

          deferreds.city = $.Deferred();
          city_input.flushCache();

          $.ajax({
            url: url,
            dataType: 'jsonp',
            success: function (response) {
              var cities = response;
              if (region == 'г Москва') {
                cities.unshift('Москва');
              } else if (region == 'г Санкт-Петербург') {
                cities.unshift('Санкт-Петербург');
              }
              city_input.autocomplete(cities, {
                delay: 2,
                minChars: 0,
                max: 110
              });

              deferreds.regions.resolve();
              deferreds.city.resolve();
            }
          });
        }

        this.fill_regions = function () {
          var country = $("#" + country_input_id).val();
          var url = kladr_host + '/selectors.json?country=' + country;

          deferreds.regions = $.Deferred();

          $.ajax({
            url: url,
            dataType: 'jsonp',
            success: function (response) {
              if (region_input_description == undefined) {
                var region_parent = $('#' + region_input_id).parent();
                if (region_parent.attr('id') == 'order_address_fields') {
                  var region_has_no_parent = true;
                  var region_input = $('#' + region_input_id);
                } else {
                  var region_input = region_parent;
                  var input_description = region_input.children('div')[0];
                }
              } else {
                var region_input = $('#regions');
                var input_description = region_input_description;
              }
              var state = region_input.find('input:first').val();
              if (region_has_no_parent && !state) state = region_input.val();
              if (!state) state = region_input.find('option:selected').val();

              var input = '<select id="' + region_input_id + '" name="' + region_input_name + '" type="text" class="' + input_class + '">';
              var regions = response.selectors[0].selector;

              for (var index in regions) {
                var obj = regions[index];
                var region_value = (obj.socr ? obj.socr + ' ' : '') + obj.name;
                var region = obj.name + (obj.socr ? ', ' + obj.socr : '');
                var selected = "";
                if (state == region_value) selected = "selected='selected'"
                input += '<option ' + selected + ' value="' + region_value + '">';
                input += region + '';
              }
              input += '</select>';
              if (region_has_no_parent) {
                region_input.replaceWith(input);
              } else {
                region_input.html(input);
              }
              if (input_description) region_input.append(input_description);
              $('#' + region_input_id).trigger('change');

              deferreds.regions.resolve();
            }
          });
        }

        return this;
      };
      (function () {



      }).call(this);
  