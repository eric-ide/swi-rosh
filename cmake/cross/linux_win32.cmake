SET(CMAKE_SYSTEM_NAME Windows)
SET(GNU_HOST i686-w64-mingw32)

set(CMAKE_C_COMPILER ${GNU_HOST}-gcc)
set(CMAKE_CXX_COMPILER ${GNU_HOST}-g++)
SET(CMAKE_RC_COMPILER ${GNU_HOST}-windres)
set(CMAKE_FIND_ROOT_PATH /usr/${GNU_HOST})

set(CMAKE_CROSSCOMPILING_EMULATOR wine)

if(NOT DEFINED MINGW_ROOT)
  set(MINGW_ROOT $ENV{MINGW32_ROOT})
endif()

set(ZLIB_ROOT ${MINGW_ROOT})
set(GMP_ROOT ${MINGW_ROOT})
set(LibUUID_ROOT ${MINGW_ROOT})
file(GLOB JAVA_HOME "$ENV{HOME}/.wine/drive_c/Program Files (x86)/Java/jdk*")
message("-- JAVA_HOME at ${JAVA_HOME}")
