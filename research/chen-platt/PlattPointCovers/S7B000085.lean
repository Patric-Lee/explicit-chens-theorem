import PlattPointSubsetKernel
import PlattPointPackets.S3B000094
import PlattPointPackets.S3B000095
import PlattPointPackets.S3B000096
import PlattPointPackets.S3B000097
import PlattPointPackets.S3B000098
import PlattPointPackets.S3B000099
import PlattPointPackets.S3B000100
import PlattGlobalGrid.S7B000085
namespace ChenEffective.PlattWindow.PointCovers.S7B000085
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((ChenEffective.PlattWindow.PointPackets.S3B000094.points ++ ChenEffective.PlattWindow.PointPackets.S3B000095.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000096.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000097.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000098.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000099.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000100.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000085.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000085.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000085
