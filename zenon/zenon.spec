%define main_version_number 0.7.2
Name:           zenon
Version:        %{main_version_number}
Release:	0
Summary:        The Zenon Theorem prover
Group:          Programming
License:        Redistribution and use in source and binary forms allowed under conditions
URL:            http://focalize.inria.fr
BuildRoot:      %{_tmppath}/%{name}-%{version}-root-%(%{__id_u} -n)
Requires:       ocaml >= 3.12
Requires:       ocaml-runtime >= 3.12
Requires:       coq >= 8.3pl2

# Here are by git base directory in which the toplevel 'focalize' dir lays.
%define sourcedir /home/didou/devel/ssurf

%description
Provides the Zenon theorem prover.

%prep
rm -Rf %{_builddir}
mkdir %{_builddir}
cp -Rf %{sourcedir}/focalize %{_builddir}

%build
cd %{_builddir}/focalize
./configure --tools_prefix /usr/bin
cd %{_builddir}/focalize/zenon
./configure --install_prefix $RPM_BUILD_ROOT/usr
make depend
make all

%install
cd %{_builddir}/focalize/zenon
# Disable sudo since we are not installing in the real final /usr.
make SUDO="" install

%clean
# Remove the source tree copied to build.
rm -Rf %{_builddir}
# Remove the temporary directory where bins and lib were stored before the
# RPM archive was fully built.
rm -Rf $RPM_BUILD_ROOT


%files
%defattr(-,root,root,755)
%doc
/usr/lib/zenon/*
/usr/bin/zenon

%changelog
