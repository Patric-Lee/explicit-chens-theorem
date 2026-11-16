import PlattPointSubsetKernel
import PlattPointPackets.S3B000077
import PlattPointPackets.S3B000078
import PlattPointPackets.S3B000079
import PlattPointPackets.S3B000080
import PlattPointPackets.S3B000081
import PlattPointPackets.S3B000082
import PlattPointPackets.S3B000083
import PlattGlobalGrid.S7B000082
namespace ChenEffective.PlattWindow.PointCovers.S7B000082
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((ChenEffective.PlattWindow.PointPackets.S3B000077.points ++ ChenEffective.PlattWindow.PointPackets.S3B000078.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000079.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000080.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000081.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000082.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000083.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000082.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000082.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000082
