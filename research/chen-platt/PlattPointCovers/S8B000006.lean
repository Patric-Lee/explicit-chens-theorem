import PlattPointSubsetKernel
import PlattPointPackets.S4B000040
import PlattPointPackets.S4B000041
import PlattPointPackets.S4B000042
import PlattPointPackets.S4B000043
import PlattPointPackets.S4B000044
import PlattPointPackets.S4B000045
import PlattPointPackets.S4B000046
import PlattPointPackets.S4B000047
import PlattPointPackets.S4B000048
import PlattGlobalGrid.S8B000006
namespace ChenEffective.PlattWindow.PointCovers.S8B000006
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((ChenEffective.PlattWindow.PointPackets.S4B000040.points ++ ChenEffective.PlattWindow.PointPackets.S4B000041.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000042.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000043.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000044.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000045.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000046.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000047.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000048.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000006.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000006.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000006
