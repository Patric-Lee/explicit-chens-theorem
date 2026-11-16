import PlattPointSubsetKernel
import PlattPointPackets.S5B000190
import PlattPointPackets.S5B000191
import PlattPointPackets.S5B000192
import PlattPointPackets.S5B000193
import PlattPointPackets.S5B000194
import PlattPointPackets.S5B000195
import PlattPointPackets.S5B000196
import PlattPointPackets.S5B000197
import PlattPointPackets.S5B000198
import PlattPointPackets.S5B000199
import PlattPointPackets.S5B000200
import PlattPointPackets.S5B000201
import PlattGlobalGrid.S8B000054
namespace ChenEffective.PlattWindow.PointCovers.S8B000054
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((ChenEffective.PlattWindow.PointPackets.S5B000190.points ++ ChenEffective.PlattWindow.PointPackets.S5B000191.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000192.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000193.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000194.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000195.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000196.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000197.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000198.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000199.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000200.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000201.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000054.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000054.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000054
