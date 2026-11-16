import PlattPointSubsetKernel
import PlattPointPackets.S3B000167
import PlattPointPackets.S3B000168
import PlattPointPackets.S3B000169
import PlattPointPackets.S3B000170
import PlattPointPackets.S3B000171
import PlattPointPackets.S3B000172
import PlattPointPackets.S3B000173
import PlattGlobalGrid.S7B000097
namespace ChenEffective.PlattWindow.PointCovers.S7B000097
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((ChenEffective.PlattWindow.PointPackets.S3B000167.points ++ ChenEffective.PlattWindow.PointPackets.S3B000168.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000169.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000170.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000171.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000172.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000173.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000097.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000097.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000097
