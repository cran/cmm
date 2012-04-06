%to do: examples

\name{ErieCounty}
\alias{ErieCounty}
\docType{data}
\title{Erie County political preference, two-wave panel}
\description{
These data come from the first systematic panel study on voting,
conducted by Lazarsfeld and his associates in Erie County, Ohio in 1940 (Lazersfeld et al, 1948;
Lazarsfeld, 1972, Wiggins, 1973, Hagenaars, 1993). The data are presented in
Table 6.3 and refer to the variables \eqn{A}{A} -- \emph{Party
preference at time 1} -- August 1940 (1.\ Republican 2.\ Democrat),
\eqn{B}{B} -- \emph{Presidential Candidate preference at time 1} (1.\ for
Willkie 2.\ against Willkie), \eqn{C}{C} -- \emph{Party preference at
time 2} -- October 1940, and \eqn{D}{D} -- \emph{Presidential Candidate
preference at time 2}. Wendell Willkie was the (defeated) 1940
Republican presidential candidate running against the Democrat
Franklin D. Roosevelt.


Section 6.3 in Bergsma, Croon, and Hagenaars (2009)

}
\usage{data(ErieCounty)}
\format{
A data frame with 266 observations on the following variables.
\describe{
\item{\code{A}}{Party Preference \eqn{T_1}{T1} (August 1940):
1 = Democrat;
2 = Republican;
}
\item{\code{B}}{Candidate Preference \eqn{T_1}{T1} (August 1940):
1 = for Willkie;
2 = against Willkie;
}
\item{\code{C}}{Party Preference \eqn{T_2}{T2} (October 1940):
1 = Democrat;
2 = Republican;
}
\item{\code{D}}{Candidate Preference \eqn{T_2}{T2} (October 1940):
1 = for Willkie;
2 = against Willkie;
}}}


\source{
CBS News and New York Times 2001.
}
\references{
 Bergsma, W. P., Croon, M. A., & Hagenaars, J. A. P. (2009).
 \emph{Marginal models for dependent, clustered, and longitudinal categorical data.}
 Berlin: Springer
}


\examples{
data(ErieCounty)

}
\keyword{datasets}
