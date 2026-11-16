import PlattPointSubsetKernel
import PlattPointPackets.S3B000055
import PlattPointPackets.S3B000056
import PlattPointPackets.S3B000057
import PlattPointPackets.S3B000058
import PlattPointPackets.S3B000059
import PlattPointPackets.S3B000060
import PlattGlobalGrid.S7B000078
namespace ChenEffective.PlattWindow.PointCovers.S7B000078
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S3B000055.points ++ ChenEffective.PlattWindow.PointPackets.S3B000056.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000057.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000058.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000059.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000060.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000078.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000078.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000078
