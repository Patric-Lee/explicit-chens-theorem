import PlattPointSubsetKernel
import PlattPointPackets.S3B000044
import PlattPointPackets.S3B000045
import PlattPointPackets.S3B000046
import PlattPointPackets.S3B000047
import PlattPointPackets.S3B000048
import PlattPointPackets.S3B000049
import PlattGlobalGrid.S7B000076
namespace ChenEffective.PlattWindow.PointCovers.S7B000076
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S3B000044.points ++ ChenEffective.PlattWindow.PointPackets.S3B000045.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000046.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000047.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000048.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000049.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000076.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000076.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000076
