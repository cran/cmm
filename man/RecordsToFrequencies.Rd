\name{RecordsToFrequencies}
\alias{RecordsToFrequencies}
\title{RecordsToFrequencies}

\description{Converts Records (units x variables) into a frequency vector.}

\usage{RecordsToFrequencies(dat, var = varDefault, dim = dimDefault, augment = "all", 
                            seed = FALSE)}

\arguments{
\item{dat}{matrix or dataframe containing the scores of units (rows) on categorical variables (columns)}
\item{var}{character or numeric vector containing variables. By default, all variables are selected.}
\item{dim}{numeric vector indicating the dimension of \code{var}. By default, the dimensions of each variable are derived from \code{dat}}
\item{augment}{augmentation: determines the type of frequency vector. Select one of four options: 
  \code{"all"} frequency vector contains all cells,
  \code{"obs"} frequency vector contains only observed cells (cells with at least one observation),
  \code{"1k"} frequency vector contains observed cells plus a selection of unobserved cells (see Van der Ark et al., 2023, for details),
  \code{"2k"} frequency vector contains observed cells plus a wider selection of unobserved cells (see Van der Ark et al., 2023).}
\item{seed}{integer. As \code{aug} options \code{"1k"} and \code{"2k"} have a random components, a setting a will allow an exact replication of a CMM analysis when option \code{"1k"} or \code{"2k"} is used.}
}

\value{
 matrix
}

\references{
  Van der Ark, L. A., Bergsma, W. P., & Koopman L. (2023)
  Maximum augmented empirical likelihood estimation of categorical marginal models for large sparse contingency tables. 
  Paper submitted for publication.
}


\author{
 W. P. Bergsma \email{w.p.bergsma@lse.ac.uk} and L. A. van der Ark \email{L.A.vanderArk@uva.nl}
}

\seealso{
\code{\link{MarginalMatrix}}
}

\examples{
data(acl)
dat <- acl[, 1:2] + 1                                 # select 2 items from ACL 
var <- 1 : ncol(dat)                                  # define the variables
marg <- Margins(var, c(0, 1))                         # margins are total (0) and 1st order 
dim <- rep(5, length(var))
t(RecordsToFrequencies(dat, var, dim, "obs"))         # frequency vector with observed cells
t(RecordsToFrequencies(dat, var, dim, "1k"))          # frequency vector with observed and
}
\keyword{univar}
