import PlattPointSubsetKernel
import PlattPointPackets.S8B000035
import PlattPointPackets.S8B000036
import PlattPointPackets.S8B000037
import PlattPointPackets.S8B000038
import PlattPointPackets.S8B000039
import PlattPointPackets.S8B000040
import PlattPointPackets.S8B000041
import PlattPointPackets.S8B000042
import PlattPointPackets.S8B000043
import PlattPointPackets.S8B000044
import PlattPointPackets.S8B000045
import PlattPointPackets.S8B000046
import PlattPointPackets.S8B000047
import PlattPointPackets.S8B000048
import PlattPointPackets.S8B000049
import PlattPointPackets.S8B000050
import PlattPointPackets.S8B000051
import PlattPointPackets.S8B000052
import PlattPointPackets.S8B000053
import PlattGlobalGrid.S8B000108
namespace ChenEffective.PlattWindow.PointCovers.S8B000108
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S8B000035.points ++ ChenEffective.PlattWindow.PointPackets.S8B000036.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000037.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000038.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000039.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000040.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000041.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000042.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000043.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000044.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000045.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000046.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000047.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000048.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000049.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000050.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000051.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000052.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000053.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000108.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000108.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000108
