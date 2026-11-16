import PlattPointSubsetKernel
import PlattPointPackets.S4B000288
import PlattPointPackets.S4B000289
import PlattPointPackets.S4B000290
import PlattPointPackets.S4B000291
import PlattPointPackets.S4B000292
import PlattPointPackets.S4B000293
import PlattPointPackets.S4B000294
import PlattPointPackets.S4B000295
import PlattPointPackets.S4B000296
import PlattPointPackets.S4B000297
import PlattPointPackets.S4B000298
import PlattGlobalGrid.S8B000034
namespace ChenEffective.PlattWindow.PointCovers.S8B000034
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((ChenEffective.PlattWindow.PointPackets.S4B000288.points ++ ChenEffective.PlattWindow.PointPackets.S4B000289.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000290.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000291.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000292.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000293.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000294.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000295.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000296.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000297.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000298.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000034.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000034.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000034
