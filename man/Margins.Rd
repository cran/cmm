\name{Margins}
\alias{Margins}
\title{Margins}

\description{Provides the required margins for selected variables}

\usage{Margins(var, k)}

\arguments{
\item{var}{vector indicating the variables}
\item{k}{vector indicating the required margin: 0 = the total, 1 = first margin, 2 =  second margin, etc. }
}

\details{
Particularly useful if for a large number of variables the same margins are required. The output can be used as argument for functions \code{\link{MarginalMatrix}}, 
\code{\link{DesignMatrix}}, and \code{\link{ConstraintMatrix}}
}

\value{
 list
}


\author{
 L. A. van der Ark \email{L.A.vanderArk@uva.nl}
}

\seealso{
\code{\link{ConstraintMatrix}}, \code{\link{MarginalMatrix}}, \code{\link{RecordsToFrequencies}}
}

\examples{
Margins(c(1, 2, 3, 4, 5), c(0, 1, 2)) # total, 1st, and 2nd margin for variables 1,.., 5
}
\keyword{univar}
