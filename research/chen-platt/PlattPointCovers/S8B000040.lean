import PlattPointSubsetKernel
import PlattPointPackets.S5B000036
import PlattPointPackets.S5B000037
import PlattPointPackets.S5B000038
import PlattPointPackets.S5B000039
import PlattPointPackets.S5B000040
import PlattPointPackets.S5B000041
import PlattPointPackets.S5B000042
import PlattPointPackets.S5B000043
import PlattPointPackets.S5B000044
import PlattPointPackets.S5B000045
import PlattPointPackets.S5B000046
import PlattPointPackets.S5B000047
import PlattGlobalGrid.S8B000040
namespace ChenEffective.PlattWindow.PointCovers.S8B000040
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((ChenEffective.PlattWindow.PointPackets.S5B000036.points ++ ChenEffective.PlattWindow.PointPackets.S5B000037.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000038.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000039.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000040.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000041.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000042.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000043.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000044.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000045.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000046.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000047.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000040.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000040.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000040
