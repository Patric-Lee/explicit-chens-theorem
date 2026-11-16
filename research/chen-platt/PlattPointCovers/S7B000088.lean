import PlattPointSubsetKernel
import PlattPointPackets.S3B000112
import PlattPointPackets.S3B000113
import PlattPointPackets.S3B000114
import PlattPointPackets.S3B000115
import PlattPointPackets.S3B000116
import PlattPointPackets.S3B000117
import PlattPointPackets.S3B000118
import PlattGlobalGrid.S7B000088
namespace ChenEffective.PlattWindow.PointCovers.S7B000088
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((ChenEffective.PlattWindow.PointPackets.S3B000112.points ++ ChenEffective.PlattWindow.PointPackets.S3B000113.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000114.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000115.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000116.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000117.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000118.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000088.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000088.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000088
