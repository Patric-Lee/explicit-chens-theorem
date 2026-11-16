import PlattPointSubsetKernel
import PlattPointPackets.S3B000161
import PlattPointPackets.S3B000162
import PlattPointPackets.S3B000163
import PlattPointPackets.S3B000164
import PlattPointPackets.S3B000165
import PlattPointPackets.S3B000166
import PlattPointPackets.S3B000167
import PlattGlobalGrid.S7B000096
namespace ChenEffective.PlattWindow.PointCovers.S7B000096
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((ChenEffective.PlattWindow.PointPackets.S3B000161.points ++ ChenEffective.PlattWindow.PointPackets.S3B000162.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000163.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000164.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000165.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000166.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000167.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000096.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000096.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000096
