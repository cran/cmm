\name{DirectSum}
\alias{DirectSum}
\title{DirectSum}

\description{Returns the direct sum of two matrices.}

\usage{DirectSum(m1, m2, p.tr = 0, p.ll = 0)}

\arguments{
\item{m1}{matrix. Top left matrix}
\item{m2}{matrix. Lower right matrix}
\item{p.tr}{numeric. Padding value for the top right matrix}
\item{p.ll}{numeric. Padding value for the lower left matrix}
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
 DirectSum(a,a)
 DirectSum(a,a,1,2)
}
\keyword{univar}
