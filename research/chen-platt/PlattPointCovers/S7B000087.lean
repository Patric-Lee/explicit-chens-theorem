import PlattPointSubsetKernel
import PlattPointPackets.S3B000106
import PlattPointPackets.S3B000107
import PlattPointPackets.S3B000108
import PlattPointPackets.S3B000109
import PlattPointPackets.S3B000110
import PlattPointPackets.S3B000111
import PlattPointPackets.S3B000112
import PlattGlobalGrid.S7B000087
namespace ChenEffective.PlattWindow.PointCovers.S7B000087
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((ChenEffective.PlattWindow.PointPackets.S3B000106.points ++ ChenEffective.PlattWindow.PointPackets.S3B000107.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000108.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000109.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000110.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000111.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000112.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000087.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000087.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000087
