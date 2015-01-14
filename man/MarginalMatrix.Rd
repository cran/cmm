\name{MarginalMatrix}
\alias{MarginalMatrix}
\title{MarginalMatrix}

\description{Returns marginal matrix; i.e., matrix required to obtained marginal frequencies}

\usage{MarginalMatrix(var, marg, dim, SubsetCoding="Identity",SelectCells="All")}

\arguments{
\item{var}{character or numeric vector containing variables}
\item{marg}{list of character or numeric indicating marginals}
\item{dim}{numeric vector indicating the dimension of \code{var}}
\item{SubsetCoding}{allows a (character) type or a matrix to be assigned to variables for each element of \code{suffconfigs},
see examples and \code{DesignMatrix}}
\item{SelectCells}{Useful option for empirical likelihood. Default "All" includes all columns, if a list of cells in the table is given only the corresponding columns of MarginalMatrix are included.}
}

\details{
Gives the matrix which, multiplied by a probability vector, gives the marginal probabilities.
The probability vector is assumed to be a vectorized form of the probabilities in a table, such that the last variable changes value fastest,
then the before last variable, etc. For example, the cells of a \eqn{2 \times 3}{2 x 3} table are arranged in vector form as (11,12,13,21,22,23).
To achieve this, the appropriate way to vectorize a data frame \code{dat} is using \code{c(t(ftable(dat)))}.

Special case of transposed \code{DesignMatrix}:
\preformatted{
 MarginalMatrix <- function(var,marg,dim,SubsetCoding="Identity")
 t(DesignMatrix(var,marg,dim,SubsetCoding=SubsetCoding,MakeSubsets=FALSE))
}
Allows weighted sums of probabilities using \code{SubsetCoding}
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
# Computing marginal frequencies
n <- c(1:6)  #example list of frequencies
var <- c("A","B")
marg <- list(c("A"),c("B"))
dim <- c(2,3)
at <- MarginalMatrix(var,marg,dim)
# list of marginal frequencies:
at %*% n

# identitymatrix: several ways of specifying:
marg <- c("A","B")
MarginalMatrix(var, marg,dim)
MarginalMatrix(var, marg, dim,
 SubsetCoding = list(c("A", "B"), list("Identity", "Identity")))
MarginalMatrix(var, marg, dim,
 SubsetCoding = list(c("A","B"), list(rbind(c(1,0),c(0,1)), rbind(c(1,0,0),c(0,1,0),c(0,0,1)))))

# omit second category of first variable
at <- MarginalMatrix(var, marg, dim,
 SubsetCoding = list(c("A","B"), list(rbind(c(1,0)),"Identity")))
at %*% n
}

\keyword{univar}
