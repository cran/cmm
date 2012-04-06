\name{DirectSum}
\alias{DirectSum}
\title{DirectSum}

\description{Returns the direct sum of two matrices.}

\usage{DirectSum(...)}

\arguments{
\item{...}{List of one or more matrices}
}

\details{
Standard mathematical direct sum operator.
}

\value{
 matrix
}

\references{
  Bergsma, W. P. (1997).
  \emph{Marginal models for categorical data}.
  Tilburg, The Netherlands: Tilburg University Press.
  \url{http://stats.lse.ac.uk/bergsma/pdf/bergsma_phdthesis.pdf}

  Bergsma, W. P., Croon, M. A., & Hagenaars, J. A. P. (2009).
  Marginal models for dependent, clustered, and longitudunal categorical data.
  Berlin: Springer.
}


\author{
 W. P. Bergsma \email{w.p.bergsma@lse.ac.uk}
}

\seealso{
\code{\link{ConstraintMatrix}}, \code{\link{DesignMatrix}}, \code{\link{DirectSum}}
}

\examples{
 a <- matrix(1:12,3,4)
 DirectSum(a)     #returns a
 DirectSum(a,a)   #returns direct sum of a and a
 DirectSum(a,a,a) #returns direct sum of a, a and a
}
\keyword{univar}
