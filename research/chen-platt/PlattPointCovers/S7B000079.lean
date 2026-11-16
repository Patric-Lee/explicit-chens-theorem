import PlattPointSubsetKernel
import PlattPointPackets.S3B000060
import PlattPointPackets.S3B000061
import PlattPointPackets.S3B000062
import PlattPointPackets.S3B000063
import PlattPointPackets.S3B000064
import PlattPointPackets.S3B000065
import PlattPointPackets.S3B000066
import PlattGlobalGrid.S7B000079
namespace ChenEffective.PlattWindow.PointCovers.S7B000079
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((ChenEffective.PlattWindow.PointPackets.S3B000060.points ++ ChenEffective.PlattWindow.PointPackets.S3B000061.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000062.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000063.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000064.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000065.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000066.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000079.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000079.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000079
