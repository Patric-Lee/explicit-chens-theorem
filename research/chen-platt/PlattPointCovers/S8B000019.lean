import PlattPointSubsetKernel
import PlattPointPackets.S4B000148
import PlattPointPackets.S4B000149
import PlattPointPackets.S4B000150
import PlattPointPackets.S4B000151
import PlattPointPackets.S4B000152
import PlattPointPackets.S4B000153
import PlattPointPackets.S4B000154
import PlattPointPackets.S4B000155
import PlattPointPackets.S4B000156
import PlattPointPackets.S4B000157
import PlattGlobalGrid.S8B000019
namespace ChenEffective.PlattWindow.PointCovers.S8B000019
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((ChenEffective.PlattWindow.PointPackets.S4B000148.points ++ ChenEffective.PlattWindow.PointPackets.S4B000149.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000150.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000151.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000152.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000153.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000154.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000155.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000156.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000157.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000019.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000019.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000019
